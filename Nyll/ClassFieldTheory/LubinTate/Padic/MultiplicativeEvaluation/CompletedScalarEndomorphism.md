# Completed standard and multiplicative scalar endomorphisms

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedScalarEndomorphism`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p`, the standard Lubin–Tate formal group over ℤ_p (for the uniformizer `p`) and the multiplicative one are compared by a power series, the standard-to-multiplicative intertwiner. This file extends that comparison and the standard scalar endomorphisms [a] to coefficients in the Witt ring W(F̄_p), and studies their evaluation, and that of the multiplicative scalar endomorphisms extended elsewhere, at topologically nilpotent points of the valuation ring of the completed level `padicCompletedLevelField p n`.

## Main definitions and results

- `padicCompletedStandardToMultiplicativeIntertwiner p`: the intertwiner with coefficients pushed to the Witt ring. It is fixed by the Witt Frobenius on coefficients (`_frobenius`), since its coefficients come from ℤ_p; it has zero constant term and admits substitution; its evaluation is injective on topologically nilpotent points (`_eval_injective`, as its linear coefficient is 1) and sends 0 to 0 (`_eval_zero`).
- `padicCompletedStandardScalarEndomorphism p a`: the standard endomorphism [a] with coefficients in the Witt ring, for `a` in the valuation ring of ℚ_p. It satisfies [a·b] = [a] ∘ [b] (`_mul`), [1] = X (`_one`), and [p] is the standard Lubin–Tate series (`_uniformizer`).
- `padicCompletedStandardToMultiplicativeIntertwiner_endomorphism`: as power series, the intertwiner composed after the standard [a] equals the multiplicative [a] composed after the intertwiner.
- `padicCompletedStandardScalarEndomorphismValue` and `padicCompletedMultiplicativeScalarEndomorphismValue`: the values of [a] at a point, again topologically nilpotent, compatible with products (`_mul`) and fixing 0 (`_zero`).
- `padicCompletedStandardScalarEndomorphismValue_uniformizer_pow`: the value of the standard [p^r] at a point is the value of the r-fold iterate of the standard Lubin–Tate polynomial.
- `padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective` and `padicCompletedStandardScalarEndomorphismValue_unit_injective`: for a unit `u`, the action of [u] is injective; for the multiplicative action, with `_one` and `_unit_after_inverse`, [u] after [u⁻¹] is the identity on points.
- `padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism`: evaluation of the intertwiner carries the standard action of [a] to the multiplicative action of [a].
- `padicCompletedLevelPowerSeriesEval_map_polynomial`: evaluating a polynomial over the valuation ring of ℚ_p as a power series agrees with polynomial evaluation.

## Proofs

The power-series identities are the identities over ℤ_p transported by Mathlib's `PowerSeries.map_subst`. Statements about values follow by compatibility of evaluation with substitution. Injectivity rests on the criterion for power series with unit linear coefficient; for the standard [u] it goes through the intertwiner and the multiplicative case.

## Points to watch

- The multiplicative scalar endomorphisms over the Witt ring and their basic properties (constant term, substitution, linear coefficient) come from other files.
- The file turns on local topological instances (the discrete uniformity on the Witt ring and the adic structure on the valuation ring of the level) defined elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeEvaluation/CompletedScalarEndomorphism.lean`: the Lean file is the source byte for byte (SHA-256 `eaa4d1b68df8f515cb9e0e8d94b4f5cc1711fc754475d7d224ea6ecd9775f0a5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
