# Determinant scaling of rectangular additive Haar measure

Author: Worker 110.

The theorem
`Langlands.HarmonicAnalysis.padicRectangularHaarScalingStatement`
proves exactly the published proposition
`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingStatement`.
The statement module and all imported modules are unchanged.

For a prime `p`, a field `F : PadicField.{uF} p`, supplied topological data
`T`, natural dimensions `r, s`, every Borel measurable structure on
`Matrix (Fin r) (Fin s) F.Carrier`, every additive Haar measure `μ`, and
`A : GeneralLinear r F.Carrier`, `B : GeneralLinear s F.Carrier`, it proves

`μ.map (fun X => A * X * B⁻¹) = (|det A|^s / |det B|^r)⁻¹ • μ`.

Here the topology is exactly `T.topology` on the field and the entrywise product
topology on matrices. Each determinant factor is the coercion to `ℝ≥0` of the
existing `T.determinantNorm`. It therefore uses the residue-normalized absolute
value of the supplied realization. The theorem adds no regularity, scalar
measurable-space, countability, or measure-normalization hypotheses.
`padicRectangularHaarScaling` exposes the same identity for direct application.

## Implemented proof

The generic part works over a topological field `K`, with its Borel measurable
structure and second countability, and a multiplicative map
`χ : K →*₀ ℝ≥0`. It assumes scalar pushforward by each nonzero `a` scales the
chosen scalar measure `ν` by `(χ a)⁻¹`. Local compactness and the Haar property
are used for transfer to arbitrary additive Haar measures.

1. `productMeasure_preserving_transvection` proves that a transvection preserves
   the finite product of a sigma-finite, translation-invariant scalar measure.
   Equality of measures is reduced to measurable rectangles. The integral of a
   rectangle indicator is disintegrated in the changed coordinate using
   `lmarginal_singleton`. The other coordinate in a transvection is distinct,
   so the resulting one-dimensional change is a translation and preserves the
   integral.
2. `productMeasure_map_diagonal` proves the determinant formula for an
   invertible diagonal. Its diagonal entries are nonzero; the scalar law applies
   to each coordinate, and the finite product of the inverse scalar factors is
   the inverse of `χ` applied to the determinant. This step does not require
   translation invariance.
3. `productMeasure_map_matrix` applies
   `Matrix.diagonal_transvection_induction_of_det_ne_zero`.
   Transvections have determinant one. Composition uses the pushforward
   composition law, the determinant product identity, and multiplication of
   measure-scaling factors.
4. `haarMeasure_map_matrix` uses additive Haar uniqueness to express an arbitrary
   Haar measure on the finite coordinate space as a scalar multiple of the
   product Haar measure. Mapping and scalar multiplication commute, so the same
   determinant factor applies. `haarMeasure_map_in_coordinates` transports
   this identity through a continuous additive equivalence, using pushforward
   Haar and cancellation with the inverse equivalence.
5. `rectangularCoordinates` is the continuous additive equivalence sending a
   matrix `X` to the function `(i,j) ↦ X i j`. The finite-sum calculation
   `rectangularCoordinates_mul` represents `X ↦ A * X * B` by the Kronecker
   matrix `A ⊗ₖ B.transpose`. The identity `Matrix.det_kronecker`, together with
   invariance of determinant under transpose, gives
   `det(A)^(card n) * det(B)^(card m)`.
   Thus `haarMeasure_map_rectangular` proves the inverse of
   `χ(det A)^(card n) * χ(det B)^(card m)` is the pushforward factor for any
   Borel additive Haar measure on `Matrix m n K`.
6. `padicRectangularHaarScaling` installs the supplied topology, valuation
   relation, and local-field structure. It obtains second countability from
   `T.secondCountableTopology` and Hausdorffness from `T.fieldT2`. It chooses
   `borel F.Carrier` and `addHaar` internally and applies the published theorem
   `padicScalarHaarScaling` to `Units.mk0 a ha` to obtain the scalar law for
   `χ = T.normalizedAbsHom`. The generic result is applied to `A` and `B⁻¹`;
   the determinant character's inverse identity gives the stated quotient.

The matrix Borel structure is an independent quantified instance in the generic
rectangular theorem and the specialization. Continuous coordinate maps give the
needed measurable maps for that instance; no equality with a chosen product
measurable structure is assumed.

## Scalar consequence and boundary cases

`padicRectangularScalarHaarScaling` states that multiplying every entry by
`a : F.Carrierˣ` pushes `μ` forward to

`((T.normalizedAbsUnits a : ℝ≥0) ^ (r * s))⁻¹ • μ`.

It applies the determinant theorem with the scalar matrix `A = a I` and `B = 1`,
uses `T.determinantNorm_scalar`, and identifies diagonal multiplication
entrywise. This is the factor `|a|^(-(r*s))`, expressed using a natural power
and inversion in `ℝ≥0`.

All finite-index arguments admit empty index types. No proof introduces
positive-dimension or nonempty-index hypotheses, so zero rows and zero columns
are retained. The closing theorem is universe-polymorphic in `uF`.

## Provenance

This is an internal proof of the prerequisite extracted in
`PadicHaarScalingStatement`, not a new transcription from external literature.
The shear integration and diagonal/transvection induction generalize the proof
pattern of Mathlib's `Real.volume_preserving_transvectionStruct` and
`Real.map_matrix_volume_pi_eq_smul_volume_pi` in
`Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` at the project's pinned Mathlib
revision. Those real Lebesgue theorems are proof-design references, not theorems
applied to the p-adic field.

The scalar normalization is supplied by the imported, published
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`; the closing theorem
does not assume the scalar proposition as a hypothesis. Haar uniqueness,
finite-product integration, matrix generation, and the Kronecker determinant
identity are imported Mathlib results. The new helpers establish the generic
change-of-variables argument and its rectangular specialization.
