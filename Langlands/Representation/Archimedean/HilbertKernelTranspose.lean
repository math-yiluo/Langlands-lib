import Langlands.Representation.Archimedean.HilbertContragredientContinuity
import Langlands.Representation.Archimedean.TransposeHaar
import Langlands.Analysis.OperatorTraceAdjoint

/-! # Compact kernel averages of the inverse-transpose Hilbert dual model -/

noncomputable section

open MeasureTheory Set Topology
open scoped Matrix.Norms.Operator InnerProduct InnerProductSpace ComplexConjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (smoothedOperator smoothedOperator_apply)
open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis.Distribution (transposeHomeomorph transposeHomeomorph_apply)

variable (F : Type*) [RCLike F] (n : ℕ)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))

local notation "GL" => Langlands.GeneralLinear n F
local notation "θ" => Langlands.GeneralLinear.inverseTranspose n F

/-- The Hilbert inverse-adjoint model pulled back by the actual inverse transpose. -/
def inverseAdjointTranspose : GL →* (H →L[ℂ] H) :=
  (hilbertContragredient R).comp (θ).toMonoidHom

/-- The inverse-transpose pullback of a jointly continuous inverse-adjoint model is continuous. -/
theorem isContinuousRepresentation_inverseAdjointTranspose (hR : IsContinuousRepresentation R) :
    IsContinuousRepresentation (inverseAdjointTranspose F n R) := by
  have h : Continuous (fun p : GL × H => hilbertContragredient R p.1 p.2) :=
    isContinuousRepresentation_hilbertContragredient (A := Matrix (Fin n) (Fin n) F) R hR
  have hp : Continuous (fun p : GL × H => (θ p.1, p.2)) :=
    ((Langlands.GeneralLinear.continuous_inverseTranspose n F).comp continuous_fst).prodMk continuous_snd
  have hc := h.comp hp
  change Continuous (fun p : GL × H => inverseAdjointTranspose F n R p.1 p.2) at hc
  exact hc

/-- Pointwise complex conjugation after ordinary transpose of the kernel variable. -/
def transposeConjugateKernel (κ : GL → ℂ) (g : GL) : ℂ := conj (κ (transposeHomeomorph n F g))

theorem continuous_transposeConjugateKernel {κ : GL → ℂ} (hκ : Continuous κ) :
    Continuous (transposeConjugateKernel F n κ) :=
  continuous_star.comp (hκ.comp (transposeHomeomorph n F).continuous)

theorem hasCompactSupport_transposeConjugateKernel {κ : GL → ℂ} (hκ : HasCompactSupport κ) :
    HasCompactSupport (transposeConjugateKernel F n κ) :=
  (hκ.comp_homeomorph (transposeHomeomorph n F)).comp_left (map_zero (starRingEnd ℂ))

variable [MeasurableSpace (Langlands.GeneralLinear n F)] [BorelSpace (Langlands.GeneralLinear n F)]
variable (μ : Measure (Langlands.GeneralLinear n F)) [μ.IsHaarMeasure] [μ.Regular]

omit [CompleteSpace H] [μ.Regular] in
private theorem integrable_inverseKernel_orbit {T : GL →* (H →L[ℂ] H)}
    (hT : IsContinuousRepresentation T) {κ : GL → ℂ}
    (hκ : Continuous κ) (hk : HasCompactSupport κ) (v : H) :
    Integrable (fun g => κ g⁻¹ • T g v) μ :=
  ((hκ.comp continuous_inv).smul (hT.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
    ((hk.comp_homeomorph (Homeomorph.inv GL)).smul_right)

omit [μ.Regular] in
private theorem inner_smoothedOperator (T : GL →* (H →L[ℂ] H))
    (hT : IsContinuousRepresentation T) {κ : GL → ℂ}
    (hκ : Continuous κ) (hk : HasCompactSupport κ) (u v : H) :
    ⟪u, smoothedOperator T μ hT κ hκ hk v⟫_ℂ = ∫ g, κ g⁻¹ * ⟪u, T g v⟫_ℂ ∂μ := by
  change (innerSL ℂ u) (∫ g, κ g⁻¹ • T g v ∂μ) = _
  rw [← (innerSL ℂ u).integral_comp_comm (integrable_inverseKernel_orbit F n μ hT hκ hk v)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => inner_smul_right _ _ _)

/-- After transpose change of variables, averaging the inverse-adjoint transpose model
is the adjoint of averaging the original action against the conjugate-transposed kernel. -/
theorem smoothedOperator_inverseAdjointTranspose (hR : IsContinuousRepresentation R)
    (κ : GL → ℂ) (hκ : Continuous κ) (hk : HasCompactSupport κ) :
    smoothedOperator (inverseAdjointTranspose F n R) μ
      (isContinuousRepresentation_inverseAdjointTranspose F n R hR) κ hκ hk =
    (smoothedOperator R μ hR (transposeConjugateKernel F n κ)
      (continuous_transposeConjugateKernel F n hκ)
      (hasCompactSupport_transposeConjugateKernel F n hk)).adjoint := by
  let e := (transposeHomeomorph n F).toMeasurableEquiv
  have he : MeasurePreserving e μ μ := measurePreserving_transpose_archimedeanGL F n μ
  have hθ (g : GL) : (θ (e g))⁻¹ = g := by
    change (θ (θ g⁻¹))⁻¹ = g
    rw [Langlands.GeneralLinear.inverseTranspose_involutive, inv_inv]
  have hinv (g : GL) : (e g)⁻¹ = transposeHomeomorph n F g⁻¹ := by
    change (θ g⁻¹)⁻¹ = θ (g⁻¹)⁻¹
    exact (map_inv (θ) g⁻¹).symm
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [inner_smoothedOperator F n μ, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, inner_smoothedOperator F n μ, ← integral_conj]
  rw [← he.integral_comp' (fun g => κ g⁻¹ * ⟪u, inverseAdjointTranspose F n R g v⟫_ℂ)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  change κ (e g)⁻¹ * ⟪u, (R ((θ (e g))⁻¹)).adjoint v⟫_ℂ =
    conj (conj (κ (transposeHomeomorph n F g⁻¹)) * ⟪v, R g u⟫_ℂ)
  rw [hθ, hinv, ContinuousLinearMap.adjoint_inner_right, map_mul, RCLike.conj_conj,
    inner_conj_symm]

/-- The covariance for trace-class averages, with conjugation correcting the Hilbert
model's conjugate-linear Riesz identification with the complex linear dual. -/
theorem operatorTrace_smoothedOperator_inverseAdjointTranspose (hR : IsContinuousRepresentation R)
    (κ : GL → ℂ) (hκ : Continuous κ) (hk : HasCompactSupport κ)
    (htr : IsTraceClass (smoothedOperator R μ hR (transposeConjugateKernel F n κ)
      (continuous_transposeConjugateKernel F n hκ)
      (hasCompactSupport_transposeConjugateKernel F n hk))) :
    operatorTrace (smoothedOperator (inverseAdjointTranspose F n R) μ
      (isContinuousRepresentation_inverseAdjointTranspose F n R hR) κ hκ hk) =
    conj (operatorTrace (smoothedOperator R μ hR (transposeConjugateKernel F n κ)
      (continuous_transposeConjugateKernel F n hκ)
      (hasCompactSupport_transposeConjugateKernel F n hk))) := by
  rw [smoothedOperator_inverseAdjointTranspose F n R μ hR κ hκ hk, operatorTrace_adjoint _ htr]

end Langlands.Archimedean
