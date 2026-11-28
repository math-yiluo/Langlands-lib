import Langlands.Representation.Plancherel.TranslatedCoefficientValue
import Langlands.Representation.Plancherel.LeviCompactCoefficients

/-! # Compact coefficient integrals under actual translation -/

noncomputable section

universe u uV uW

open MeasureTheory
open scoped TensorProduct
open Langlands

namespace Langlands.Plancherel.TranslatedCoefficientValue

open Aubert.General Induction ActualConjugateLeviTensor

private theorem conjugateValue_pairing
    {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
    {M N : Subgroup H} (g : H)
    (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (A : SmoothRep.{0, u, uV} ℂ M) (v : CoefficientTensor A) :
    TensorProduct.lift (smoothDualPairing ((conjugationFunctor g hM).obj A).representation).flip
        (conjugateValue g hM A v) =
      TensorProduct.lift (smoothDualPairing A.representation).flip v := by
  have h : (TensorProduct.lift
      (smoothDualPairing ((conjugationFunctor g hM).obj A).representation).flip).comp
        (conjugateValue g hM A).toLinearMap =
      TensorProduct.lift (smoothDualPairing A.representation).flip := by
    apply TensorProduct.ext'
    intro a ℓ
    rfl
  exact LinearMap.congr_fun h v

section Integral

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  {P M U Q N W : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) (g : K)
  (hP : ∀ x : H, x ∈ Q ↔ (g : H)⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ (g : H)⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ (g : H)⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ N)
  (e : ((conjugationFunctor (g : H) hM).obj A).representation.Equiv B.representation)
  [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

set_option quotPrecheck false in
local notation "L" => CoefficientConjugation.leviCoefficientLeftTranslation
  h k (g : H) hP hM hW hc hc' hu hu' A

set_option maxHeartbeats 800000 in
/-- Actual product left translation by a compact point and the inducing
equivalence preserve the coefficient integral over the same compact. -/
theorem integral_leviIntegrand_translated
    (f : leviProductInducedCoefficientObject h hc A) (x : H) :
    (∫ l : K, CompactInduction.leviIntegrand k hc' B K x
        (coefficientCongr k hc' hu' e (L f)) l ∂CompactInduction.measure K hK) =
      ∫ l : K, CompactInduction.leviIntegrand h hc A K x f l ∂CompactInduction.measure K hK := by
  let : BorelSpace K := inferInstanceAs (BorelSpace (K : Subgroup H))
  let : ContinuousMul K := inferInstanceAs (ContinuousMul (K : Subgroup H))
  let : MeasurableMul K :=
    ⟨fun _ => (continuous_const.mul continuous_id).measurable,
      fun _ => (continuous_id.mul continuous_const).measurable⟩
  calc
    _ = ∫ l : K, CompactInduction.leviIntegrand h hc A K x f (g⁻¹ * l)
          ∂CompactInduction.measure K hK := by
      apply integral_congr_ae
      filter_upwards [] with l
      simp only [CompactInduction.leviIntegrand, leviProductInducedCoefficientIntegrand,
        LinearMap.coe_mk, AddHom.coe_mk]
      have he := translatedProduct_eval h k (g : H) hP hM hW hc hc' hu hu' A B e f
        ((l : H) * x, (l : H))
      refine (congrArg
        (fun v : CoefficientTensor B => TensorProduct.lift (smoothDualPairing B.representation).flip v)
        he).trans ?_
      rw [productCoefficientLeviEquiv_pairing, conjugateValue_pairing]
      have harg : ((g : H), (g : H))⁻¹ * ((l : H) * x, (l : H)) =
          (((g⁻¹ * l : K) : H) * x, (g⁻¹ * l : K).val) :=
        Prod.ext (mul_assoc _ _ _).symm rfl
      exact congrArg (fun p : H × H => TensorProduct.lift (smoothDualPairing A.representation).flip
        (Induction.eval (P.prod P) (leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
          (productLeviObject A A.contragredient)) f p)) harg
    _ = _ := integral_mul_left_eq_self _ g⁻¹

end Integral

end Langlands.Plancherel.TranslatedCoefficientValue
