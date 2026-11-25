# Upper ramification groups are locally constant from the left

Module `FontaineWintenberger.Ramification.Upper.LocallyConstant`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `G` be a finite group acting by ring automorphisms on a discrete valuation ring `R`. The file contains one theorem on the upper ramification groups of this action.

`exists_upperRamificationGroup_eq_left`: for every real `u > 0` there is `v` with `0 < v < u` such that `upperRamificationGroup G w = upperRamificationGroup G u` for all `w` in the half-open interval `(v, u]`. The endpoint `u` is included, also when `u` is a jump of the filtration.

The proof puts `t = inverseHerbrandFunction G u` and `n = ⌈t⌉`. The real-indexed lower group depends only on the ceiling of its index, and the inverse Herbrand function is strictly increasing on `[-1, ∞)`. So for `w ≤ u` larger than `herbrandFunction G (n - 1)`, the inverse Herbrand function of `w` lies in `(n - 1, n]` and the group is the same.

The statement depends on the library's ceiling convention for real-indexed lower groups. Nothing is said to the right of `u`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/LocallyConstant.lean` (SHA-256 of the source file `19c20d5cdfa213d7e5ecf59decfa26b8cbc3e8ecb7989d65efd47751951ef1d4`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
