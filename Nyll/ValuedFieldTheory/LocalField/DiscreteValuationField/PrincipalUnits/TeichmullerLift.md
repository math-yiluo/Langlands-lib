# The Teichmüller lift, and a coefficient field in equal characteristic

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a field `K` with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O, and finite residue field k with q elements. The file defines the Teichmüller lift k → O, a multiplicative section of reduction, and shows that when O has characteristic p it is also additive, so that it gives a coefficient field: a ring homomorphism k → O splitting reduction.

## Main definitions and results

- `residueTeichmullerLift F`: sends 0 to 0 and y ≠ 0 to the unique (q − 1)-st root of unity in O with residue y.
- `residueTeichmullerLift_zero`, `..._one`, `..._mul`: it preserves 0, 1 and products. `residueMap_residueTeichmullerLift`: its residue is y.
- `residueTeichmullerLift_pow_card` and `residueTeichmullerLift_isRoot_X_pow_card_sub_X`: every lift satisfies T^q = T.
- `residueTeichmullerLift_add_of_charP`: if O has characteristic p (`CharP F.valuationSubring p`, p prime) and q = p^n, then the lift is additive.
- `residueTeichmullerRingHomOfCharP`: under the same hypotheses, the lift as a ring homomorphism k → O; `residueMap_comp_residueTeichmullerRingHomOfCharP` states that reduction composed with it is the identity. `residueTeichmullerFieldHomOfCharP` is the composite k → K.

## Proofs

In characteristic p, the sum of two lifts is again a root of T^q − T, because (a + b)^(p^n) = a^(p^n) + b^(p^n). The derivative of T^q − T is −1, a unit, so Hensel uniqueness (two roots with the same residue coincide) identifies this sum with the lift of x + y.

## Points to note

- Additivity and the coefficient field are proved only in equal characteristic: they need `CharP` of the valuation ring and an explicit hypothesis that the residue field has p^n elements. In mixed characteristic only multiplicativity is available here.
- The lift is a plain function k → O, with value 0 at 0 by a case split; it is multiplicative on all of k, and is bundled as a homomorphism only in `residueTeichmullerRingHomOfCharP`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/TeichmullerLift.lean`: the Lean file is the source byte for byte (SHA-256 `adddc8ad60a78bd6def196cb5251297b98a807fc769018dbb82ee676202f42d7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
