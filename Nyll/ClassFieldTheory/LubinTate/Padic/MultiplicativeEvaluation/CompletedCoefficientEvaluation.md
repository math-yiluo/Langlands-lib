# Coefficient maps and evaluation on completed p-adic Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedCoefficientEvaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p` and a level `n`, this file provides the maps from the valuation ring of ℚ_p into the completed Lubin–Tate level `padicCompletedLevelField p n` and its valuation ring, which are used to evaluate polynomials and power series with p-adic coefficients. With them it records that the chosen completed primitive point is a torsion point of exact level n + 1, and proves an injectivity criterion for evaluation of power series whose linear coefficient is a unit.

## Main definitions and results

- `padicCompletedLevelField_padicAlgebra` (instance) and `padicCompletedLevelField_padicScalarTower`: the completed level as a ℚ_p-algebra through the completed unramified field.
- `padicCompletedLevelPadicFieldCoefficientHom` and `padicCompletedLevelPadicIntegerCoefficientHom`: the coefficient map from the valuation ring of ℚ_p into the completed level, with values in the field or in its valuation ring; `_coe` and `padicCompletedLevelPadicIntegerPolynomialEval_coe` say the two agree, also after polynomial evaluation.
- `padicCompletedPrimitiveRoot_iterate_succ_eq_zero` and `padicCompletedPrimitiveRoot_iterate_ne_zero`: the chosen primitive point is a root of the (n + 1)-fold iterate of the standard Lubin–Tate polynomial for the uniformizer `p`, and not a root of the n-fold iterate. `padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero` and `_iterate_ne_zero` are the same statements in the valuation ring.
- `padicCompletedLevelPowerSeriesEval_congr_point`: evaluation of a power series does not depend on the proof that the point is topologically nilpotent.
- `padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient`: if a power series `f` over the Witt ring has zero constant term and a unit linear coefficient, then evaluation of `f` at topologically nilpotent points of the valuation ring of the level is injective.

## Proofs

The torsion relation at level n + 1 comes from the factorization of the (n + 1)-fold iterate through the primitive polynomial, of which the point is a root. If the n-fold iterate vanished at the point, the equation of the primitive polynomial (a power of the n-fold iterate plus `p`) would force `p = 0`. Injectivity uses the compositional inverse of `f` given by Mathlib's `PowerSeries.substInvOfIsUnit`: substituting it back recovers `X`, so evaluation at `f(x)` recovers `x`.

## Points to watch

- The Witt ring carries the discrete uniformity, as a local instance of low priority; the valuation ring of the level carries the maximal-ideal-adic topology, with local instances for completeness and Hausdorffness. Other files of the library turn these local instances on by name.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeEvaluation/CompletedCoefficientEvaluation.lean`: the Lean file is the source byte for byte (SHA-256 `fef10de88bb0b6269dcdfa101c5b27fa4e3be8605527f523c7f12bd08f167768`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
