import Langlands.Representation.Archimedean.SmoothDualEvaluation
import Langlands.Representation.Archimedean.HilbertKernelTranspose
import Langlands.Analysis.OperatorTraceConjugate

/-! # The complex-linear continuous Hilbert dual and transpose kernel traces -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator InnerProductSpace ComplexConjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (smoothedOperator)
open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis.Distribution (transposeHomeomorph)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Hilbert structure on the continuous complex-linear dual, with its
existing operator norm and the inner product induced by the conjugate-linear Riesz map. -/
scoped instance continuousDualInnerProductSpace : InnerProductSpace ℂ (StrongDual ℂ H) where
  inner L M := ⟪(InnerProductSpace.toDual ℂ H).symm M, (InnerProductSpace.toDual ℂ H).symm L⟫_ℂ
  norm_sq_eq_re_inner L := by
    change ‖L‖ ^ 2 = RCLike.re (inner ℂ ((InnerProductSpace.toDual ℂ H).symm L)
      ((InnerProductSpace.toDual ℂ H).symm L))
    calc
      ‖L‖ ^ 2 = ‖(InnerProductSpace.toDual ℂ H).symm L‖ ^ 2 := by
        rw [LinearIsometryEquiv.norm_map]
      _ = _ := norm_sq_eq_re_inner (𝕜 := ℂ) _
  conj_inner_symm L M := inner_conj_symm _ _
  add_left L M N := by
    change ⟪(InnerProductSpace.toDual ℂ H).symm N, (InnerProductSpace.toDual ℂ H).symm (L + M)⟫_ℂ = _
    rw [map_add, inner_add_right]
  smul_left L M c := by
    change ⟪(InnerProductSpace.toDual ℂ H).symm M, (InnerProductSpace.toDual ℂ H).symm (c • L)⟫_ℂ = _
    rw [map_smulₛₗ, inner_smul_right]

/-- Riesz identifies the original Hilbert inner product with the conjugated dual
inner product. -/
theorem inner_toDual_toDual (x y : H) :
    ⟪InnerProductSpace.toDual ℂ H x, InnerProductSpace.toDual ℂ H y⟫_ℂ = conj ⟪x, y⟫_ℂ := by
  change ⟪(InnerProductSpace.toDual ℂ H).symm ((InnerProductSpace.toDual ℂ H) y),
    (InnerProductSpace.toDual ℂ H).symm ((InnerProductSpace.toDual ℂ H) x)⟫_ℂ = _
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply, inner_conj_symm]

variable (F : Type*) [RCLike F] (n : ℕ)
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))

local notation "GLF" => Langlands.GeneralLinear n F
local notation "θ" => Langlands.GeneralLinear.inverseTranspose n F
local notation "D" => StrongDual ℂ H

/-- The inverse-transpose pullback of the action on complex-linear continuous functionals. -/
def inverseTransposeContinuousDual : GLF →* (D →L[ℂ] D) :=
  (continuousDualRepresentation R).comp (θ).toMonoidHom

/-- The continuous dual action stays jointly continuous under inverse transpose. -/
theorem isContinuousRepresentation_inverseTransposeContinuousDual (hR : IsContinuousRepresentation R) :
    IsContinuousRepresentation (inverseTransposeContinuousDual F n R) :=
  (isContinuousRepresentation_continuousDual R hR).comp
    (((Langlands.GeneralLinear.continuous_inverseTranspose n F).comp continuous_fst).prodMk
      continuous_snd)

variable [MeasurableSpace (Langlands.GeneralLinear n F)] [BorelSpace (Langlands.GeneralLinear n F)]
  (μ : Measure (Langlands.GeneralLinear n F)) [μ.IsHaarMeasure] [μ.Regular]

omit [μ.Regular] in
/-- The Riesz map conjugates the averaged inverse-adjoint model to the genuine dual
average, with conjugation of the scalar weight. -/
theorem smoothedOperator_inverseTransposeContinuousDual (hR : IsContinuousRepresentation R)
    (κ : GLF → ℂ) (hκ : Continuous κ) (hk : HasCompactSupport κ) :
    smoothedOperator (inverseTransposeContinuousDual F n R) μ
      (isContinuousRepresentation_inverseTransposeContinuousDual F n R hR) κ hκ hk =
    conjugateHilbertOperator (InnerProductSpace.toDual ℂ H)
      (smoothedOperator (inverseAdjointTranspose F n R) μ
        (isContinuousRepresentation_inverseAdjointTranspose F n R hR)
        (fun g => conj (κ g)) (continuous_star.comp hκ)
        (hk.comp_left (map_zero (starRingEnd ℂ)))) := by
  let e := InnerProductSpace.toDual ℂ H
  let L := e.toContinuousLinearEquiv.toContinuousLinearMap
  let S := inverseAdjointTranspose F n R
  let U := inverseTransposeContinuousDual F n R
  have hS : IsContinuousRepresentation S :=
    isContinuousRepresentation_inverseAdjointTranspose F n R hR
  have hc : Continuous fun g : GLF => conj (κ g⁻¹) := continuous_star.comp (hκ.comp continuous_inv)
  have hsupp : HasCompactSupport fun g : GLF => conj (κ g⁻¹) :=
    (hk.comp_homeomorph (Homeomorph.inv GLF)).comp_left (map_zero (starRingEnd ℂ))
  have hσ (r : ℝ) (z : ℂ) : conj (r • z) = r • conj z := by
    simp only [Algebra.smul_def, map_mul]
    change conj (Complex.ofReal r) * conj z = Complex.ofReal r * conj z
    rw [Complex.conj_ofReal]
  apply ContinuousLinearMap.ext
  intro L₀
  obtain ⟨x, rfl⟩ := e.surjective L₀
  rw [conjugateHilbertOperator_apply]
  have hi : Integrable (fun g : GLF => conj (κ g⁻¹) • S g x) μ :=
    (hc.smul (hS.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
      hsupp.smul_right
  change (∫ g, κ g⁻¹ • U g (e x) ∂μ) = L (∫ g, conj (κ g⁻¹) • S g x ∂μ)
  rw [← L.integral_comp_commSL hσ hi]
  apply integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  change κ g⁻¹ • U g (e x) = L (conj (κ g⁻¹) • S g x)
  rw [map_smulₛₗ, Complex.conj_conj]
  exact congrArg (κ g⁻¹ • ·) (toDual_hilbertContragredient R (θ g) x).symm

set_option maxHeartbeats 600000 in
/-- The genuine complex-linear dual after inverse transpose has the trace of
the original action on the ordinary-transposed compact kernel. -/
theorem traceClass_and_trace_inverseTransposeContinuousDual (hR : IsContinuousRepresentation R)
    (κ : GLF → ℂ) (hκ : Continuous κ) (hk : HasCompactSupport κ)
    (htr : IsTraceClass (smoothedOperator R μ hR (κ ∘ transposeHomeomorph n F)
      (hκ.comp (transposeHomeomorph n F).continuous)
      (hk.comp_homeomorph (transposeHomeomorph n F)))) :
    IsTraceClass (smoothedOperator (inverseTransposeContinuousDual F n R) μ
      (isContinuousRepresentation_inverseTransposeContinuousDual F n R hR) κ hκ hk) ∧
    operatorTrace (smoothedOperator (inverseTransposeContinuousDual F n R) μ
      (isContinuousRepresentation_inverseTransposeContinuousDual F n R hR) κ hκ hk) =
    operatorTrace (smoothedOperator R μ hR (κ ∘ transposeHomeomorph n F)
      (hκ.comp (transposeHomeomorph n F).continuous)
      (hk.comp_homeomorph (transposeHomeomorph n F))) := by
  let η := κ ∘ transposeHomeomorph n F
  let T := smoothedOperator R μ hR η
    (hκ.comp (transposeHomeomorph n F).continuous) (hk.comp_homeomorph (transposeHomeomorph n F))
  let w : GLF → ℂ := fun g => conj (κ g)
  have hw : Continuous w := continuous_star.comp hκ
  have hwc : HasCompactSupport w := hk.comp_left (map_zero (starRingEnd ℂ))
  have he : smoothedOperator R μ hR (transposeConjugateKernel F n w)
      (continuous_transposeConjugateKernel F n hw) (hasCompactSupport_transposeConjugateKernel F n hwc)
      = T := by
    apply ContinuousLinearMap.ext
    intro x
    change (∫ g, transposeConjugateKernel F n w g⁻¹ • R g x ∂μ) =
      ∫ g, η g⁻¹ • R g x ∂μ
    apply integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    change conj (conj (κ (transposeHomeomorph n F g⁻¹))) • R g x = η g⁻¹ • R g x
    simp only [Complex.conj_conj, η, Function.comp_apply]
  rw [smoothedOperator_inverseTransposeContinuousDual F n R μ hR κ hκ hk,
    smoothedOperator_inverseAdjointTranspose F n R μ hR w hw hwc, he]
  have ht := isTraceClass_adjoint T htr
  refine ⟨isTraceClass_conjugateHilbertOperator _ inner_toDual_toDual _ ht, ?_⟩
  rw [operatorTrace_conjugateHilbertOperator _ inner_toDual_toDual _ ht,
    operatorTrace_adjoint T htr, Complex.conj_conj]

end Langlands.Archimedean
