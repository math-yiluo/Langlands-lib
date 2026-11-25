# Extending an integer-indexed filtration to the real line

Module `Nyll.ValuedFieldTheory.Ramification.Filtration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a descending sequence of subgroups `F 0 ⊇ F 1 ⊇ …` of a group `G`, the file defines the real-indexed filtration `t ↦ F ⌈t⌉`, its right limits and its jumps, and shows that jumps occur only at natural numbers. It is generic infrastructure for filtrations such as that of principal units.

- `natCeilStepFiltration F t = F ⌈t⌉₊`, the natural-number ceiling.
- `natCeilStepFiltrationAfter F t`: the supremum of the groups at indices `s > t`.
- `IsNatCeilStepFiltrationJump F t`: the group at `t` differs from its right limit.

For `F` antitone:

- `natCeilStepFiltration_antitone`, `natCeilStepFiltrationAfter_le`: the extension is antitone and the right limit lies in the group at `t`.
- `natCeilStepFiltrationAfter_natCast`: at `t = n` the right limit is `F (n + 1)`; so `n` is a jump iff `F n ≠ F (n + 1)`.
- `isNatCeilStepFiltrationJump_integer`: every jump is a natural number.

## Watch for

The natural ceiling is `0` for `t ≤ 0`, so the filtration equals `F 0` on the negative reals.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Filtration.lean`: the Lean file is the source byte for byte (SHA-256 `02043f7c2810c1d658503d3375a8eedf8d1818956143487ee83226c797b10f39`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
