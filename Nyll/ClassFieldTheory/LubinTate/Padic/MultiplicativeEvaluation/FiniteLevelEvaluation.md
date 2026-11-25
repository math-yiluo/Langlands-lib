# Evaluating the p-adic multiplicative comparison at finite levels

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelEvaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p`, take the finite standard Lubin–Tate levels over ℚ_p built from the uniformizer `p` (`padicMultiplicativeLubinTateSeries_isUniformizer p`), and the power series H = `padicStandardToMultiplicativeIntertwiner p` over ℤ_p that compares the standard Lubin–Tate series with the multiplicative series (1 + X)ᵖ − 1. This file evaluates H at topologically nilpotent points of the valuation ring of a finite level and transfers to these values the identities H satisfies as power series.

## Main definitions and results

- `padicMultiplicativePrimitivePoint p n`: the value of H at the chosen standard primitive point of the level, topologically nilpotent (`_hasEval`).
- `padicMultiplicativeLubinTateSeries_eval`: evaluating the multiplicative Lubin–Tate series at `x` gives (1 + x)ᵖ − 1.
- `padicStandardToMultiplicativeIntertwiner_eval_functionalEquation`: for every topologically nilpotent `x`, the multiplicative series evaluated at H(x) equals H evaluated at the standard series of `x`.
- `padicStandardToMultiplicativeIntertwiner_eval_endomorphism`: H carries the standard action of a scalar `a` of ℤ_p to the action of the multiplicative-series endomorphism with the same coefficient (the `recursiveIntertwiner` of the multiplicative series with itself for `a`).
- `padicMultiplicativeToStandardIntertwiner_eval_comp`: evaluating the reverse comparison `padicMultiplicativeToStandardIntertwiner p` at H(x) gives back `x`.
- `padicStandardToMultiplicativeIntertwiner_eval_zero` and `_eval_injective`: H sends 0 to 0, and its evaluation is injective on topologically nilpotent points.

## Proofs

Each of the three composition statements is the corresponding power-series identity (functional equation, intertwining of endomorphisms, reverse comparison composed with H equals X), proved elsewhere, combined with the compatibility of evaluation with substitution. The formula (1 + x)ᵖ − 1 comes from Mathlib's `PowerSeries.binomialSeries_nat`, and H(0) = 0 from the divisibility of H by X. Injectivity follows from the left inverse given by the reverse comparison.

## Points to watch

- The topologies are local instances: the discrete uniformity on the coefficient ring and the maximal-ideal-adic topology on the valuation ring of the level, with completeness and Hausdorffness derived from the completeness of the level.
- The statements are for the single uniformizer `p` of ℚ_p, although some local instances are stated for a general local field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeEvaluation/FiniteLevelEvaluation.lean`: the Lean file is the source byte for byte (SHA-256 `52e911b3e06e052617e30b0552b9827f87b519be1cce58b228044fd1186d6add`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
