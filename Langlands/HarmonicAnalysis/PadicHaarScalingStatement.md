# Residue-normalized additive Haar change of variables

Author: Worker 117.

This module states two internal prerequisites for the published proposition
`Langlands.GLBlockModulusHaarStatement`. It supplies no proof of either
prerequisite; both are proved by separate published theorems (see
[Status](#status)). All three declarations are transparent proposition
definitions.

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
multiplication contributes `det(B)^(-r)`. This module does not prove the
determinant calculation or the Haar identity, and they are not premises
assumed in the statements; the separate theorem
`padicRectangularHaarScalingStatement` proves the rectangular identity.

For an upper block unipotent radical, Levi conjugation acts on the `(i,j)`
coordinate by `X_ij ↦ m_i X_ij m_j⁻¹`. The rectangular factors therefore match
the factors in the existing `T.leviModulus`. Applying them to the nonabelian
radical still requires a separate proof that its product coordinate measure is
Haar; nothing in this module asserts that step. Both identities use pushforward
measure, which accounts for the inverse absolute value.

## Status

- `PadicScalarHaarScalingStatement.{uF}` is proved by the theorem
  `Langlands.HarmonicAnalysis.padicScalarHaarScalingStatement.{uF}` in
  `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`, whose type is
  exactly that proposition. The proof is artifact
  `391187ae-1d4c-4be0-804e-2fe896a2d21e` version 1, published at Library
  commit `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed`.
- `PadicRectangularHaarScalingStatement.{uF}` is proved by the theorem
  `Langlands.HarmonicAnalysis.padicRectangularHaarScalingStatement.{uF}` in
  `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`, whose type is
  exactly that proposition. The proof is artifact
  `4d3a028e-4ed8-4805-8c24-ae917bdb9606` version 1, published at Library
  commit `dd9f9be571b3d712bb77031f3e6347bebd97a214`.

Each proof's validation passed the Lake build and exact-target checks, and an
independent review approved it. Both keep the arbitrary field universe and
add no hypothesis. The conjunction `PadicAdditiveHaarScalingStatement` has no
separately named or published proof. It follows immediately by pairing the
two theorems,
`⟨padicScalarHaarScalingStatement, padicRectangularHaarScalingStatement⟩`.
Neither proof asserts that the product coordinate measure on a nonabelian
block unipotent radical is Haar.
