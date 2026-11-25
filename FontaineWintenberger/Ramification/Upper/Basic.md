# Upper ramification groups and Herbrand's theorem

Module `FontaineWintenberger.Ramification.Upper.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file defines the upper numbering of ramification groups for a finite group `G` acting on a discrete valuation ring `R`, and proves its compatibility with quotients.

`upperRamificationGroup G u`, for real `u`, is the real-indexed lower group `lowerRamificationGroupReal G (maximalIdeal R)` at the index `inverseHerbrandFunction G u`. It is normal, antitone on `[-1, ∞)`, equal to `G` at `-1` and to inertia at `0`, and trivial for large `u` when the action is faithful.

`fixedField_map_upperRamificationGroup` (Herbrand's theorem): let `K` be a complete discretely valued field with perfect residue field, `L/K` finite Galois and `H` a normal subgroup. For `u ≥ -1`, restriction to the fixed field of `H` maps the upper group at `u` of `L ≃ₐ[K] L` onto that of the fixed field. `fixedField_quotient_upperRamificationGroup` states this through the quotient by `H`.

Both follow from the statement for lower groups and transitivity of the inverse Herbrand function.

The Galois group of the fixed field appears as the decomposition subgroup of its valuation ring.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/Basic.lean` (SHA-256 of the source file `8aff7019e85a632a0ecb7d27f3db6adbe4c97731ae937d1b00c42601f83ecc5b`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
