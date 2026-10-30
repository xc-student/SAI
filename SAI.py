from z3 import *
import re
import time
from pathlib import Path


class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.room_capacities = []
        self.exams_to_students = []


def read_file(filename):
    instance = Instance()

    with open(filename, encoding="utf-8-sig") as f:
        def read_attribute(name):
            line = f.readline()
            pattern = rf"{re.escape(name)}:\s*(\d+)"
            match = re.fullmatch(pattern, line.strip())

            if match is None:
                raise ValueError(
                    f"Could not parse line {line!r}; "
                    f"expected the attribute: {name}"
                )

            return int(match.group(1))

        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams = read_attribute("Number of exams")
        instance.number_of_slots = read_attribute("Number of slots")
        instance.number_of_rooms = read_attribute("Number of rooms")

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(
                read_attribute(f"Room {r} capacity")
            )

        for line in f:
            if not line.strip():
                continue

            match = re.fullmatch(r"\s*(\d+)\s+(\d+)\s*", line)
            if match is None:
                raise ValueError(
                    f"Could not parse the exam-student pair: {line!r}"
                )

            exam, student = map(int, match.groups())

            if not 0 <= exam < instance.number_of_exams:
                raise ValueError(f"Exam ID out of range: {exam}")

            if not 0 <= student < instance.number_of_students:
                raise ValueError(f"Student ID out of range: {student}")

            instance.exams_to_students.append((exam, student))

    return instance


def validate_schedule(
    instance,
    schedule,
    students_by_exam,
    unavailable_rooms,
    allowed_slots,
    max_parallel_exams,
):
    """Independently validate all constraints using ordinary Python."""
    n_exams = instance.number_of_exams
    n_slots = instance.number_of_slots
    n_rooms = instance.number_of_rooms

    if set(schedule) != set(range(n_exams)):
        raise ValueError("The schedule does not cover all exams")

    occupied = set()
    exams_per_slot = [0] * n_slots

    for e, (slot, room) in schedule.items():
        if not (0 <= slot < n_slots and 0 <= room < n_rooms):
            raise ValueError(
                f"Exam {e} has an invalid slot or room ID"
            )

        if (slot, room) in occupied:
            raise ValueError(
                "Multiple exams occupy the same room in the same slot"
            )
        occupied.add((slot, room))

        if len(students_by_exam[e]) > instance.room_capacities[room]:
            raise ValueError(
                f"Exam {e} exceeds the room capacity"
            )

        if slot in unavailable_rooms.get(room, set()):
            raise ValueError(
                f"Exam {e} uses a room during an unavailable slot"
            )

        if e in allowed_slots and slot not in allowed_slots[e]:
            raise ValueError(
                f"Exam {e} is scheduled outside its allowed slots"
            )

        exams_per_slot[slot] += 1

    for e1 in range(n_exams):
        for e2 in range(e1 + 1, n_exams):
            if students_by_exam[e1] & students_by_exam[e2]:
                difference = abs(schedule[e1][0] - schedule[e2][0])
                if difference < 2:
                    raise ValueError(
                        f"Exams {e1} and {e2} share students but are "
                        "scheduled in the same or consecutive slots"
                    )

    if max_parallel_exams is not None:
        if any(count > max_parallel_exams for count in exams_per_slot):
            raise ValueError(
                "The number of simultaneous exams exceeds the limit"
            )


def solve(
    instance,
    unavailable_rooms=None,
    allowed_slots=None,
    max_parallel_exams=None,
):
    """
    Additional constraint parameters:
    unavailable_rooms: {room ID: set of unavailable slot IDs}
    allowed_slots: {exam ID: set of allowed slot IDs}
    max_parallel_exams: maximum number of exams allowed in each slot

    If a parameter is omitted, its corresponding restriction is not applied.
    """
    total_start = time.perf_counter()

    unavailable_rooms = {
        r: set(slots)
        for r, slots in (unavailable_rooms or {}).items()
    }
    allowed_slots = {
        e: set(slots)
        for e, slots in (allowed_slots or {}).items()
    }

    n_exams = instance.number_of_exams
    n_slots = instance.number_of_slots
    n_rooms = instance.number_of_rooms

    # Validate additional settings to avoid silently ignoring invalid IDs.
    for room, slots in unavailable_rooms.items():
        if not 0 <= room < n_rooms:
            raise ValueError(
                f"Invalid room ID in additional settings: {room}"
            )
        if any(not 0 <= slot < n_slots for slot in slots):
            raise ValueError(
                f"Room {room} has an invalid unavailable slot ID"
            )

    for exam, slots in allowed_slots.items():
        if not 0 <= exam < n_exams:
            raise ValueError(
                f"Invalid exam ID in additional settings: {exam}"
            )
        if any(not 0 <= slot < n_slots for slot in slots):
            raise ValueError(
                f"Exam {exam} has an invalid allowed slot ID"
            )

    if max_parallel_exams is not None:
        if (
            not isinstance(max_parallel_exams, int)
            or max_parallel_exams < 0
        ):
            raise ValueError(
                "The simultaneous exam limit must be a non-negative integer"
            )

    solver = Solver()

    exam_slots = [Int(f"slot_{e}") for e in range(n_exams)]
    exam_rooms = [Int(f"room_{e}") for e in range(n_exams)]

    students_by_exam = [set() for _ in range(n_exams)]
    for exam, student in instance.exams_to_students:
        students_by_exam[exam].add(student)

    # Main constraint 1:
    # Each exam has exactly one valid slot and one valid room.
    # Each integer variable takes a single value, so no additional
    # "exactly one" constraint is required.
    for e in range(n_exams):
        solver.add(
            exam_slots[e] >= 0,
            exam_slots[e] < n_slots,
            exam_rooms[e] >= 0,
            exam_rooms[e] < n_rooms,
        )

    # Main constraint 2: The assigned room must have sufficient capacity.
    for e in range(n_exams):
        candidates = len(students_by_exam[e])

        for r in range(n_rooms):
            if candidates > instance.room_capacities[r]:
                solver.add(exam_rooms[e] != r)

    for e1 in range(n_exams):
        for e2 in range(e1 + 1, n_exams):
            # Main constraint 3:
            # At most one exam can occupy a room in a given slot.
            solver.add(
                Or(
                    exam_slots[e1] != exam_slots[e2],
                    exam_rooms[e1] != exam_rooms[e2],
                )
            )

            if students_by_exam[e1] & students_by_exam[e2]:
                # Main constraint 4:
                # A student cannot take two exams in the same slot.
                solver.add(exam_slots[e1] != exam_slots[e2])

                # Main constraint 5:
                # A student cannot take exams in consecutive slots.
                # Combined with constraint 4, this is equivalent to
                # requiring an absolute slot difference of at least 2.
                solver.add(
                    exam_slots[e1] != exam_slots[e2] + 1,
                    exam_slots[e2] != exam_slots[e1] + 1,
                )

    # Additional constraint 1:
    # Specified rooms are unavailable during specified slots.
    for room, slots in unavailable_rooms.items():
        for slot in slots:
            for e in range(n_exams):
                solver.add(
                    Or(
                        exam_rooms[e] != room,
                        exam_slots[e] != slot,
                    )
                )

    # Additional constraint 2:
    # Specified exams must take place within their allowed slots.
    for exam, slots in allowed_slots.items():
        solver.add(
            Or([exam_slots[exam] == slot for slot in slots])
        )

    # Additional constraint 3:
    # Limit the number of simultaneous exams in each slot.
    if max_parallel_exams is not None:
        for slot in range(n_slots):
            solver.add(
                Sum([
                    If(exam_slots[e] == slot, 1, 0)
                    for e in range(n_exams)
                ]) <= max_parallel_exams
            )

    build_end = time.perf_counter()

    # Measure the satisfiability check separately.
    check_start = time.perf_counter()
    result = solver.check()
    check_end = time.perf_counter()

    schedule = None

    if result == sat:
        print("sat")
        model = solver.model()
        schedule = {}

        for e in range(n_exams):
            slot = model.eval(
                exam_slots[e], model_completion=True
            ).as_long()
            room = model.eval(
                exam_rooms[e], model_completion=True
            ).as_long()
            schedule[e] = (slot, room)

        validate_schedule(
            instance,
            schedule,
            students_by_exam,
            unavailable_rooms,
            allowed_slots,
            max_parallel_exams,
        )

        for e, (slot, room) in sorted(
            schedule.items(),
            key=lambda item: (item[1][0], item[1][1], item[0]),
        ):
            print(f"Exam {e}: Slot {slot}, Room {room}")

        print("Schedule validation: passed")

    elif result == unsat:
        print("unsat")

    else:
        print("unknown")
        print("Reason:", solver.reason_unknown())

    total_end = time.perf_counter()

    build_ms = (build_end - total_start) * 1000
    check_ms = (check_end - check_start) * 1000
    total_ms = (total_end - total_start) * 1000

    print(f"Preprocessing and model construction time: {build_ms:.3f} ms")
    print(f"Satisfiability check time: {check_ms:.3f} ms")
    print(
        f"Total time (including output and validation): "
        f"{total_ms:.3f} ms"
    )

    return {
        "status": str(result),
        "schedule": schedule,
        "build_ms": build_ms,
        "check_ms": check_ms,
        "total_ms": total_ms,
    }


if __name__ == "__main__":
    base_dir = Path(__file__).resolve().parent

    # Test both satisfiable and unsatisfiable instances.
    for prefix in ("sat", "unsat"):
        for i in range(1, 11):
            filename = base_dir / f"{prefix}{i}.txt"

            if not filename.is_file():
                continue

            print(f"\nTesting: {filename.name}")
            instance = read_file(filename)
            solve(instance)