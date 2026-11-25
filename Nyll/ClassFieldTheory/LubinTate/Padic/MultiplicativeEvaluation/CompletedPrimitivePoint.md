# The completed multiplicative primitive point

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedPrimitivePoint`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p` and a level `n`, the completed level `padicCompletedLevelField p n` contains a chosen primitive point λ for the standard Lubin–Tate series with uniformizer `p`. Evaluating at λ the power series that intertwines the standard and the multiplicative formal groups (with coefficients in the Witt ring W(F̄_p)) gives a point of the multiplicative formal group. This file shows that this point has exact torsion level n + 1, both for `p` and for a changed uniformizer `u·p` with `u` a p-adic unit, and defines the action of units on it.

## Main definitions and results

- `padicCompletedMultiplicativePrimitivePoint p n`: the value at λ of `padicCompletedStandardToMultiplicativeIntertwiner p`, an element of the valuation ring of the completed level; `_hasEval` says it is topologically nilpotent, hence a valid evaluation point.
- `padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_succ_eq_zero` and `_uniformizer_pow_ne_zero`: the multiplicative scalar endomorphism for p^(n+1) kills the point, and that for pⁿ does not.
- `padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_succ_eq_zero` and `_changedUniformizer_pow_ne_zero`: the same with p replaced by the changed uniformizer `standardLubinTateChangedUniformizer` built from `p` and a unit `u` of the valuation ring of ℚ_p.
- `padicCompletedMultiplicativeUnitEndomorphism p u`: the multiplicative scalar endomorphism for the unit `u`, as a power series over the Witt ring, which admits substitution (`_hasSubst`).
- `padicCompletedMultiplicativePrimitivePointUnitAction p u n`: its value at the multiplicative primitive point, again topologically nilpotent (`_hasEval`).

## Proofs

The intertwiner carries the standard scalar endomorphisms to the multiplicative ones on evaluation. On the standard side, the endomorphism for p^k evaluates as the k-fold iterate of the standard Lubin–Tate polynomial, so the torsion relations for λ proved earlier transfer; the non-vanishing uses that evaluation of the intertwiner is injective and sends 0 to 0. For the changed uniformizer, the endomorphism for (u·p)^k is that for p^k followed by that for u^k, and the latter is injective on evaluation points because u^k is a unit.

## Points to watch

- The "changed uniformizer" here is the product of `u` and `p`; the torsion statements for it are deduced from those for `p`, not from a separate Lubin–Tate construction.
- The file turns on local topological instances (the discrete uniformity on the Witt ring, the adic structure on the valuation ring of the level) defined in another file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeEvaluation/CompletedPrimitivePoint.lean`: the Lean file is the source byte for byte (SHA-256 `24e0f94ab700c3ad7f8b1f800c2658a685d13a8ec65011a92dc7d6762802ed1d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
