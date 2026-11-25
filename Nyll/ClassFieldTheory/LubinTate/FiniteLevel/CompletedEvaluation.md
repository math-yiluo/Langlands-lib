# Evaluating power series in a standard Lubin–Tate level

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` and `π` a uniformizer. The endomorphisms `[a]` of the standard Lubin–Tate formal module are genuine power series with coefficients in the valuation ring `O_F`. This file evaluates power series over `O_F` in the complete valuation ring `O_n` of the standard finite level `n`, and in particular evaluates `[a]` at the chosen primitive division point.

## Main definitions and results

- `standardLubinTateLevelCoefficientHom`: the canonical ring map `O_F → O_n`, which is the field inclusion `K → L_n` on elements.
- `standardLubinTateLevelPowerSeriesEval hπ n x hx`: the ring homomorphism `O_F⟦X⟧ → O_n` evaluating at an `x` that is topologically nilpotent (`PowerSeries.HasEval x`). It sends `X` to `x`, constants through the coefficient map, agrees with polynomial evaluation on polynomials, is continuous, and commutes with substitution of a series admitting substitution (`standardLubinTateLevelPowerSeriesEval_subst`).
- `standardLubinTatePrimitivePointInteger_hasEval`: the chosen primitive point is a uniformizer of `O_n`, hence a valid evaluation point; `standardLubinTatePrimitivePointEvaluation` is evaluation there.
- `standardLubinTateEndomorphismEvalAt` and `standardLubinTateEndomorphismValue`: the value `[a](x)`, and the value of `[a]` at the primitive point. These values are again topologically nilpotent; `[1]` gives the point itself, `[0]` gives `0`, and `[ab](x) = [a]([b](x))` (`standardLubinTateEndomorphismEvalAt_mul`, `standardLubinTateEndomorphismValue_mul`).

## Proof

Evaluation is Mathlib's `PowerSeries.eval₂Hom`. The compatibility with substitution comes from Mathlib's multivariable `eval₂_subst`, and multiplicativity of `[a]` from composition of the Lubin–Tate endomorphisms.

## Points to watch

- The topologies are local instances of this file: `O_F` is given the discrete uniformity and `O_n` its maximal-ideal-adic topology, for which it is complete and Hausdorff. Other files using these evaluations must use the same topologies.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/CompletedEvaluation.lean`: the Lean file is the source byte for byte (SHA-256 `da872204c74dcaf6f429c64e03c5a0ae3c1eda0954f5bedf896020a7c4421108`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
