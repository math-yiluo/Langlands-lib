# Coordinates of the field of norms at full upper stages

Module `FontaineWintenberger.FieldOfNorms.Relative.UpperStage`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsPerfectResidueLocalField K`, with residue characteristic `p`, and let `L/K` be separable algebraic. For a finite intermediate field `E` and a real `b`, the file studies the condition that the APF subgroup of `L/E` at upper parameter `b` is the whole Galois group. Under it, the `E`-coordinate of a norm-compatible family is a ring homomorphism modulo a power of the maximal ideal.

## Full upper stages

- `FiniteIntermediateField.HasFullUpper E b`: `apfSubgroup E _ b = ⊤` for the image of `L` in a separable closure of `E`; the embedding does not matter (`hasFullUpper_iff_embedding`).
- `hasFullUpper_iff_stage_le`: for `b ≥ 0`, equivalent to `apfFiniteStage K L (apfPhi K E b) ≤ E`.
- `HasFullUpper.of_le`: passage to smaller nonnegative parameters.
- `IsAPF.exists_finiteIntermediateField_fullUpper_tail`: for `L/K` APF and `b ≥ 0`, every `E` above some finite `T` satisfies it; `IsAPF.exists_monotone_cofinal_fullUpper_stages` gives a monotone cofinal sequence with prescribed depths.
- For `b > 0` and finite `F ⊇ E`: the residue inclusion is surjective (`residue_surjective`, APF assumed), `[F : E]` is a power of `p` (`finrank_eq_prime_pow`), and `b ≤ apfRamificationBound E F` (`le_relativeFirstBound`).
- `FieldOfNorms.valuation_eq_coordinate_of_fullUpper`: for `b > 0` and `L/K` APF, the valuation of a norm family is the normalized valuation of its `E`-coordinate.

## Projections

Here `L/K` is APF and infinite, `b > 0`, `r ≤ ⌈(p − 1)/p · b⌉`.

- `HasFullUpper.truncatedNorm`: the surjective ring homomorphism `𝒪_F/𝔪^s → 𝒪_E/𝔪^r` (`r ≤ s`) induced by the norm.
- `FieldOfNorms.integralCoordinateAt E`: the `E`-coordinate of an integral norm family, a plain function into `𝒪_E`.
- `FieldOfNorms.highBreakProjection`: the ring homomorphism from the valuation ring of the field of norms to `𝒪_E/𝔪^r` given by reducing the `E`-coordinate; it composes `FieldOfNorms.truncation` at a deep stage with the truncated norm. It is surjective, with kernel the `r`-th power of the maximal ideal (`ker_highBreakProjection`).

## Discriminants

- `FieldOfNorms.coordinatePolynomial E f`: the polynomial over `𝒪_E` whose coefficients are the coordinates of those of `f`; monic of the same degree when `f` is, and congruent modulo `𝔪^r` to the image of `f` under `highBreakProjection`.
- `coordinatePolynomial_discr_valuation`: for monic `f` with discriminant of valuation greater than `exp(−r)`, the discriminant of the coordinate polynomial has the same normalized valuation; that polynomial is then separable over `E` (`separable_coordinatePolynomial`).
- `exists_cofinal_coordinatePolynomial_discr_stable`: along some monotone cofinal sequence `F n` with full upper stage `n + 1`, both hold eventually for every monic `f` separable over the field of norms.

## Points to watch

- `integralCoordinateAt` is not additive; only its reductions are ring homomorphisms.
- Infinitude of `L/K` is `Fact (¬ Module.Finite K L)`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/UpperStage.lean` (SHA-256 of the source file `84b96a768f73182488b07e2403e35fd2c233118b6eba3ed2bed8a98abd36f222`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
