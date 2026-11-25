# Changed-uniformizer evaluation on completed p-adic levels

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Fix a prime `p`, a unit `u` of ℤ_p (the valuation ring of ℚ_p) and a level `n`. The changed uniformizer is the product of `u` and `p`, and `padicChangedUniformizerIntertwiner p u` is a power series over the Witt ring W(F̄_p) comparing the multiplicative formal group with the standard Lubin–Tate group of the changed uniformizer. Evaluating it at the completed multiplicative primitive point gives a point θ of the completed level `padicCompletedLevelField p n`; this file shows θ is a primitive torsion point for the changed uniformizer and relates it to the Frobenius.

## Main definitions and results

- `padicChangedUniformizerThetaValue p u n`: the point θ, topologically nilpotent (`_hasEval`).
- `padicCompletedChangedStandardScalarEndomorphismValue`: the action of the endomorphisms [a] of the changed standard group on points; compatible with products, [1] acts trivially, and the r-th power of the changed uniformizer acts by the r-fold changed standard iterate (`_uniformizer_pow`).
- `padicChangedUniformizerIntertwiner_endomorphism_evaluation`: evaluating the intertwiner after the multiplicative [a] equals the changed standard [a] after the intertwiner; `_changedSeries_evaluation` is the case of the changed uniformizer itself.
- `padicChangedUniformizerIntertwiner_eval_injective` and `_eval_zero`: evaluation of the intertwiner is injective on topologically nilpotent points (its linear coefficient is a Witt unit) and sends 0 to 0.
- `padicChangedUniformizerThetaValue_iterate_succ_eq_zero` and `_iterate_ne_zero`: θ is killed by the (n + 1)-fold changed iterate and not by the n-fold one.
- `padicChangedUniformizerThetaValue_isRoot`, `_field_isRoot` and `_aeval_levelMinpoly`: θ is a root of the changed primitive Lubin–Tate polynomial, in the valuation ring and in the field, hence of the minimal polynomial of the generator of the changed finite level.
- `padicChangedUniformizerLevelEmbedding p u n`: the ℚ_p-algebra embedding of the finite Lubin–Tate level of the changed uniformizer into the completed level, sending its power-basis generator to θ (`_apply_gen`).
- `padicChangedUniformizerIntertwiner_frobenius_evaluation` and `padicChangedUniformizerThetaValue_frobeniusCoefficients`: applying the Witt Frobenius to the coefficients of the intertwiner and evaluating at a topologically nilpotent point x is the same as evaluating the intertwiner at the multiplicative [u](x); at the primitive point this gives the intertwiner evaluated at the unit action of `u`.

## Proofs

The torsion statements are transported from those of the multiplicative primitive point through the intertwining identity, using injectivity of evaluation for the lower bound. The primitive-polynomial equation follows by factoring the (n + 1)-fold iterate through the n-fold iterate and the primitive polynomial. The embedding lifts a power basis along a root of its minimal polynomial.

## Points to watch

- The power-series identities used here, in particular the Frobenius identity, are proved in other files and imported.
- θ lives in the completed level built from the uniformizer `p`, not in a separate completed level for the changed uniformizer.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeEvaluation/Core.lean`: the Lean file is the source byte for byte (SHA-256 `a5086f2ba93ab20f8e8229d6281dde5297ecfde65fb14aefbc15bea0a691225f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
