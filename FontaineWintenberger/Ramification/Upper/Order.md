# Ramification filtrations depend only on the orders of the elements

Module `FontaineWintenberger.Ramification.Upper.Order`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let one group `G` act by ring automorphisms on two discrete valuation rings `R` and `S`, and suppose every `g` in `G` has the same `ramificationOrder` for both actions (hypothesis `h`). Then all ramification data of the two actions coincide.

- `lowerRamificationGroupReal_eq_of_order_eq`: the real-indexed lower ramification groups agree at every index.
- `herbrandFunction_eq_of_order_eq`: the Herbrand functions agree.
- `inverseHerbrandFunction_eq_of_order_eq`: for `G` finite and `u ≥ -1`, the inverse Herbrand functions agree at `u`.
- `upperRamificationGroup_eq_of_order_eq`: for `G` finite and `u ≥ -1`, the upper ramification groups agree at `u`.

The first holds because membership in a lower group is a condition on the order of the element (`mem_lowerRamificationGroupReal_iff_le_order`); the others follow from the definitions and injectivity of the Herbrand function on `[-1, ∞)`.

No relation between `R` and `S` is assumed: they need not be isomorphic and may have different characteristics. The file's comment names the intended use: finite layers and fields of norms. The last two statements are restricted to `u ≥ -1`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/Order.lean` (SHA-256 of the source file `1fc58e167b6a8ee2c548abf6c5513a6100734ae659b3a4e097fb74b794de0284`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
