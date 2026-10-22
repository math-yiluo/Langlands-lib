# Residue-normalized additive Haar change of variables

Author: Worker 117.

This module states two internal prerequisites for the published proposition
`Langlands.GLBlockModulusHaarStatement`. It supplies no proof of either
prerequisite. All three declarations are transparent proposition definitions.

`Langlands.HarmonicAnalysis.PadicScalarHaarScalingStatement` says that for every
prime `p`, every `F : PadicField p`, every supplied realization
`T : F.TopologicalData`, every Borel measurable structure for exactly
`T.topology`, every additive Haar measure `μ`, and every field unit `a`,

`μ.map (fun x => a * x) = |a|⁻¹ • μ`.

The positive scalar is the coercion of the existing `T.normalizedAbsUnits a`
to `ℝ≥0`. Thus `|a|` is exactly the residue-normalized absolute value from
`NormalizedCharacter`, not a freely chosen absolute value or a Haar character
defined by the desired equation. There is no regularity, measure-normalization,
countability, or extra field-realization hypothesis.

`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingStatement` quantifies over
the same field and realization, every pair of natural dimensions `r, s`, every
Borel measurable structure on the rectangular matrix space with its entrywise
product topology, every additive Haar measure on that space, and invertible
matrices `A` and `B` of ranks `r` and `s`. It states

`μ.map (fun X => A * X * B⁻¹) = (|det A|^s / |det B|^r)⁻¹ • μ`.

The determinant factors are exactly the published `T.determinantNorm`. Zero
rows and zero columns are included. The matrix space is then a singleton and
the displayed factor is one. No measurable structure on the scalar field is
required by the rectangular clause; the quantified measurable structure is on
the matrix space itself.

`Langlands.HarmonicAnalysis.PadicAdditiveHaarScalingStatement` is the conjunction
of these two proposition definitions. The components are named separately so
that their proofs can be developed and reviewed separately.

## Internal provenance and intended use

These are mathematical subproblems extracted from the block-modulus proof,
not a transcription of a separate literature theorem. The scalar normalization
is the one already fixed by `PadicField.TopologicalData` and
`Langlands.Group.GL.NormalizedCharacter`. The rectangular formula is the
finite-dimensional change-of-variables identity for the linear transformation
`X ↦ A X B⁻¹`: left multiplication contributes `det(A)^s`, and inverse-right
multiplication contributes `det(B)^(-r)`. This determinant calculation and the
Haar identity remain proof obligations. They are not premises assumed in the
statements.

For an upper block unipotent radical, Levi conjugation acts on the `(i,j)`
coordinate by `X_ij ↦ m_i X_ij m_j⁻¹`. The rectangular factors therefore match
the factors in the existing `T.leviModulus`. Applying them to the nonabelian
radical still requires a separate proof that its product coordinate measure is
Haar; nothing in this module asserts that step. Both identities use pushforward
measure, which accounts for the inverse absolute value.
