import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform
import Langlands.Representation.Plancherel.CoefficientTensorPullback

/-! # Fourier transport for the Levi model comparison in VIII.2.1 -/

noncomputable section

universe u uV

open MeasureTheory Langlands.Plancherel
open scoped TensorProduct

namespace Langlands.HarishChandraSchwartz

variable {G H : Type u} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  {A : SmoothRep.{0, u, uV} ℂ G} {B : SmoothRep.{0, u, uV} ℂ H}
  (e : H ≃ₜ* G) (eA : (SmoothRep.pullback e A).representation.Equiv B.representation)

private def inducingLinearEquiv : A ≃ₗ[ℂ] B := eA.toLinearEquiv

private theorem coefficientTensorToEnd_modelTransport (t : CoefficientTensor A) (v : A) :
    coefficientTensorToEnd B (coefficientTensorCongr eA (coefficientTensorPullbackEquiv e A t))
        (inducingLinearEquiv e eA v) =
      inducingLinearEquiv e eA (coefficientTensorToEnd A t v) := by
  induction t using TensorProduct.inductionOn with
  | tmul w l =>
    have ht :=
      (congrArg (coefficientTensorCongr eA) (coefficientTensorPullbackEquiv_tmul e A w l)).trans
        (coefficientTensorCongr_tmul (A := SmoothRep.pullback e A) (B := B)
          eA w (smoothDualPullbackEquiv e A l))
    rw [ht, coefficientTensorToEnd_tmul, coefficientTensorToEnd_tmul]
    have hl : (contragredientMap eA.symm.toIntertwiningMap
        (smoothDualPullbackEquiv e A l)).val (inducingLinearEquiv e eA v) = l.val v :=
      congrArg (smoothDualPullbackEquiv e A l).val
        (eA.symm_apply_apply (v : SmoothRep.pullback e A))
    rw [hl, map_smul]
    rfl
  | add t s ht hs => simp only [map_add, LinearMap.add_apply, ht, hs]

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  [Nonempty (CompactOpenSubgroup G)] [Nonempty (CompactOpenSubgroup H)]
  {muG : Measure G} {muH : Measure H}
  [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  [muH.IsMulLeftInvariant] [muH.IsMulRightInvariant]
  {XiG sigmaG : G → ℝ} {XiH sigmaH : H → ℝ}
  (hwG : L2Weights muG XiG sigmaG) (hwH : L2Weights muH XiH sigmaH)
  (hA : IsAdmissible A.representation) (hB : IsAdmissible B.representation)
  (hTG : HasTemperedCoefficients XiG sigmaG A.representation)
  (hTH : HasTemperedCoefficients XiH sigmaH B.representation)
  (hXiG : ∀ g, XiG g⁻¹ = XiG g) (hSigmaG : ∀ g, sigmaG g⁻¹ = sigmaG g)
  (hXiH : ∀ h, XiH h⁻¹ = XiH h) (hSigmaH : ∀ h, sigmaH h⁻¹ = sigmaH h)

/-- A measure-preserving Levi model identification preserves the normalized
coefficient Fourier transform of a pulled-back function. The input function
may have an extra scalar, as occurs in the III.6 diagram. The common `degree`
is the formal degree once the quotient Haar normalizations are compared. -/
def ConstantTermFourierModelTransportStatement : Prop :=
  MeasurePreserving e muH muG →
    ∀ (degree : ℝ) (fG : Space XiG sigmaG) (fH : Space XiH sigmaH) (c : ℂ),
      (∀ h, fH h = c * fG (e h)) →
        coefficientFourierTransform B hwH hB hTH hXiH hSigmaH degree fH =
          c • coefficientTensorCongr eA
            (coefficientTensorPullbackEquiv e A
              (coefficientFourierTransform A hwG hA hTG hXiG hSigmaG degree fG))

theorem coefficientFourierTransform_eq_smul_of_modelTransport :
    ConstantTermFourierModelTransportStatement e eA hwG hwH hA hB hTG hTH
      hXiG hSigmaG hXiH hSigmaH := by
  intro hmu degree fG fH c hf
  apply coefficientTensorToEnd_injective B
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (inducingLinearEquiv e eA).surjective v
  have htransport := coefficientTensorToEnd_modelTransport e eA
    (coefficientFourierTransform A hwG hA hTG hXiG hSigmaG degree fG) w
  rw [map_smul, coefficientTensorToEnd_coefficientFourierTransform,
    LinearMap.smul_apply, LinearMap.smul_apply, htransport,
    coefficientTensorToEnd_coefficientFourierTransform, LinearMap.smul_apply,
    LinearEquiv.map_smul, smul_comm c (degree : ℂ)]
  congr 1
  apply ext_smoothDual hB.1
  intro l
  let lA := (smoothDualPullbackEquiv e A).symm (smoothContragredientEquiv eA l)
  have hl (x : A) : lA.val x = l.val (inducingLinearEquiv e eA x) := rfl
  rw [map_smul, schwartzAction_eval, ← hl, schwartzAction_eval, smul_eq_mul]
  let integrand : G → ℂ :=
    fun g => c * (Space.check hXiG hSigmaG fG g * lA.val (A.representation g w))
  calc
    _ = ∫ h : H, integrand (e h) ∂muH := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun h => by
        have he : inducingLinearEquiv e eA (A.representation (e h) w) =
            B.representation h (inducingLinearEquiv e eA w) :=
          congrArg (fun L : SmoothRep.pullback e A →ₗ[ℂ] B => L w) (eA.isIntertwining' h)
        simp only [integrand, hl, he, Space.coe_check, check_apply, hf, map_inv, mul_assoc]
    _ = ∫ g : G, integrand g ∂muG :=
      hmu.integral_comp e.toHomeomorph.measurableEmbedding _
    _ = _ := integral_const_mul _ _

end Langlands.HarishChandraSchwartz
