# Haar measure under linear automorphisms over a nonarchimedean local field

The module `Langlands.HarmonicAnalysis.LinearHaarScaling` computes how additive Haar measure on a
finite-dimensional vector space over a nonarchimedean local field transforms under linear
automorphisms, in terms of Mathlib's modulus `distribHaarChar`.

## Content

Let `F` be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`, any
characteristic). Mathlib's `distribHaarChar F : Fˣ →* ℝ≥0` is the modulus of `F`: the factor
`|a|_F` by which `x ↦ a x` multiplies Haar measure. Pushing a Haar measure forward along `x ↦ a x`
divides it by `|a|_F` (`map_mul_left_addHaar`), and `|a|_F = 1` when `a` is a unit of the
valuation ring (`distribHaarChar_eq_one_of_valuation_eq_one`).

- `map_linearEquiv_addHaar`: for a finite-dimensional `F`-vector space `V` with its module
  topology (`IsModuleTopology F V`), an additive Haar measure `μ` on `V` and an `F`-linear
  automorphism `T`,

  `μ.map T = (distribHaarChar F (det T))⁻¹ • μ`.

  The proof passes to coordinates `V ≅ Fⁿ` along a basis and applies the Library's determinant
  change of variables `haarMeasure_map_in_coordinates`
  (`Langlands/HarmonicAnalysis/PadicRectangularHaarScalingProof.lean`), which reduces to diagonal
  matrices and transvections, with the scalar law above extended by `0` at `0`.
- `map_mul_left_addHaar_algebra`: for a finite `F`-algebra `E` with its module topology and
  `z ∈ Eˣ`, multiplication by `z` divides Haar measure on `E` by `|N_{E/F}(z)|_F`, because the
  determinant of multiplication by `z` is the norm.
- `det_restrictScalars_mul_mul` and `map_mul_mul_addHaar`: for a finite extension field `E` of
  `F`, `u ∈ GL_α(E)`, `a ∈ GL_ν(E)`, the `F`-linear map `x ↦ u x a` of `M_{α×ν}(E)` has
  determinant `N(det u)^{|ν|} N(det a)^{|α|}` (the `E`-determinant is that of the Kronecker product
  `u ⊗ aᵀ`, and the `F`-determinant of an `E`-linear map is the norm of its `E`-determinant), so it
  divides Haar measure by `|N det u|_F^{|ν|} |N det a|_F^{|α|}`. The map itself is
  `mulMulEquiv F u a : Matrix α ν E ≃ₗ[F] Matrix α ν E` (`mulMulEquiv_apply`:
  `mulMulEquiv F u a x = u * x * a`). The instance `isModuleTopology_matrix F α ν :
  IsModuleTopology F (Matrix α ν E)` gives the module topology on matrices.
- `eq_smul_addHaar_of_map_mul_left`: a measure `n` on `F` with `n {0} = 0`, finite on compact
  sets, with `n.map (u * ·) = |u|_F⁻¹ • n` for all units `u`, is a multiple of Haar measure. The
  proof compares `n(A) λ(𝒪ˣ)` and `n(𝒪ˣ) λ(A)` by integrating the function
  `(x, y) ↦ 1_A(x) |x|⁻¹ 1_{𝒪ˣ}(x⁻¹ y)` in both orders (Tonelli). This is used for the Gauss
  integral of the norm form of a quadratic extension
  (`Langlands/Theta/WeilIndex/NormForm.lean`).

Comparison with the Library's absolute values:

- `distribHaarChar_eq_absUnits`: for the absolute value of the Library's
  `GeneralScalarHaarScalingStatement` (normalized by `|ϖ| = q⁻¹` on a uniformizer and `1` on units
  of the valuation ring), `distribHaarChar F a = |a|`. It is deduced from the Library's proof of
  that statement (`generalScalarHaarScalingStatement`), evaluating both scaling laws on the valuation
  ring.
- `generalRectangularHaarScalingStatement_of_map_linearEquiv`: the Library's
  `GeneralRectangularHaarScalingStatement` (`X ↦ A X B⁻¹` on `M_{r×s}(F)`) follows from
  `map_mul_mul_addHaar` with `E = F`. So the two theorems do not stand unrelated: the Library's
  rectangular law is the special case of the linear one.

For p-adic fields given as the Library's `PadicField` structures, the comparison of
`distribHaarChar` with `LocalFieldData.normalizedAbs` is the private lemma
`distribHaarChar_eq_normalizedAbsUnits` of
`Langlands/HarmonicAnalysis/PadicScalarHaarScalingProof.lean`; it is not needed here.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, files under
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`:
`MapLinearEquivAddHaarLocalField.lean` (`map_linearEquiv_haar`, whole, with another proof of the
coordinate step), `MapMulLeftEqNormSmul.lean` (whole), `MapTwoSidedMulHaarMatrixQuadraticExt.lean`
(whole), `DetRestrictScalarsTwoSidedMatrixMul.lean` (whole), `HomogeneousMeasureEqSmulAddHaarLocalField.lean`
(whole), and from `Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean` the statement of
`nabs_eq_one_of_valuation_eq_one` (lines 134–141). The repository has no licence file; the text is
used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `GlobalTheory.KSp.Homog` → `Langlands.HarmonicAnalysis` (public)
  and `Langlands.HarmonicAnalysis.LinearHaarScaling.Internal` (the helpers of the homogeneity
  lemma).
- Renamed: `map_linearEquiv_haar` → `map_linearEquiv_addHaar`, `map_mul_left_eq_norm_smul` →
  `map_mul_left_addHaar_algebra`, `map_twoSided_haar` → `map_mul_mul_addHaar`,
  `det_restrictScalars_twoSidedMul` → `det_restrictScalars_mul_mul`, `eq_smul_haar_of_homog` →
  `eq_smul_addHaar_of_map_mul_left`, `nabs_eq_one_of_valuation_eq_one` →
  `distribHaarChar_eq_one_of_valuation_eq_one`.
- The source's coordinate computation (`smul_map_mulVec_pi`, `IsLocallyConstantAddChar.lean`
  lines 105–146, an induction over diagonal matrices and transvections) is replaced by the
  Library's `haarMeasure_map_in_coordinates`, which is the same induction.
- Hypotheses dropped: `[CharZero F]` (unused), and the quadratic involution of `E` (only its
  consequence `FiniteDimensional F E` is used). `F`, `V`, `E`, `α`, `ν` in any universe.
- The source's wrapper `nabs` is replaced by `distribHaarChar`; the
  local-field facts (second countability, compactness and openness of `𝒪`) are the Library's
  `GeneralLocalField.*`.
- New: `map_mul_left_addHaar` (stated in the source only inside proofs), `isModuleTopology_matrix`,
  `distribHaarChar_eq_absUnits`, `generalRectangularHaarScalingStatement_of_map_linearEquiv`.

## Declarations

- `map_mul_left_addHaar`, `distribHaarChar_eq_one_of_valuation_eq_one`
- `map_linearEquiv_addHaar`
- `map_mul_left_addHaar_algebra`
- `det_restrictScalars_mul_mul`, `mulMulEquiv`, `mulMulEquiv_apply`, `isModuleTopology_matrix`
  (an instance), `map_mul_mul_addHaar`
- `eq_smul_addHaar_of_map_mul_left`
- `distribHaarChar_eq_absUnits`, `generalRectangularHaarScalingStatement_of_map_linearEquiv`

All in the namespace `Langlands.HarmonicAnalysis`.

## Dependencies

`Langlands.HarmonicAnalysis.GeneralHaarScalingProof` (and through it
`PadicRectangularHaarScalingProof` for `haarMeasure_map_in_coordinates`,
`GeneralScalarHaarScalingProof` for `GeneralLocalField.*` and `generalScalarHaarScalingStatement`,
`GeneralHaarScalingStatement`); Mathlib: `MeasureTheory.Measure.Haar.DistribChar`,
`LinearAlgebra.Matrix.Kronecker`, `Topology.Algebra.Module.ModuleTopology`,
`RingTheory.Norm.Transitivity`.
