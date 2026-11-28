import Langlands.Representation.Plancherel.TranslatedCoefficientValueForm
import Langlands.Representation.Plancherel.CompactProductIntegralFormula
import Langlands.Representation.Plancherel.LeviCompactCoefficients

/-! # Compact product forms under actual translation -/

noncomputable section

universe u uV uW

open MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel.TranslatedCoefficientValue

open Aubert.General Induction HarishChandraSchwartz ActualConjugateLeviTensor

set_option maxHeartbeats 900000 in
set_option maxRecDepth 4096 in
private theorem leviProductForm_inner_integral_integral
    {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    {P M U : Subgroup H} [LocallyCompactSpace P]
    (h : IsSemidirectDecomposition P M U) (hc : IsClosed (U : Set H))
    (A : SmoothRep.{0, u, uV} ℂ M) (K : OpenSubgroup H) (hu : IsUnimodularModulus U hc)
    (hK : IsCompact (K : Set H)) (hP : IsClosed (P : Set H))
    (hPK : ∀ g : H, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hH : ∀ g : H, Measure.modularCharacter g = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hc P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hcof : CompactOpenCofinal M) (b : InvariantPositiveForm A.representation)
    (F J : leviProductInducedCoefficientObject h hc A) :
    (CompactInduction.leviProductForm h hc A K hu hK hP hPK hH hδ hA hcof b).inner F J =
      ∫ k : K, ∫ l : K, (coefficientTensorInvariantForm A hcof hA b).inner
        (Induction.eval (P.prod P) (leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
          (productLeviObject A A.contragredient)) F ((k : H), (l : H)))
        (Induction.eval (P.prod P) (leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
          (productLeviObject A A.contragredient)) J ((k : H), (l : H)))
        ∂CompactInduction.measure K hK ∂CompactInduction.measure K hK := by
  let E := productInducedCoefficientLeviEquiv h hc A hu
  change (CompactInduction.productForm h hc hP K hK hPK hH hδ A hcof hA b).inner
    (E.symm F) (E.symm J) = _
  refine (CompactInduction.productForm_inner_integral_integral h hc hP K hK hPK hH hδ A
    hcof hA b (E.symm F) (E.symm J)).trans ?_
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  let evaluate := Induction.eval (P.prod P)
    (leviInflatedInducingRepresentation (h.prod h) (hc.prod hc) (productLeviObject A A.contragredient))
  have hvalue (v : leviProductInducedCoefficientObject h hc A) :=
    (productInducedCoefficientLeviEquiv_eval h hc A hu (E.symm v) ((x : H), (y : H))).symm.trans
      (congrArg (fun w => evaluate w ((x : H), (y : H))) (E.apply_symm_apply v))
  exact congrArg₂ (coefficientTensorInvariantForm A hcof hA b).inner (hvalue F) (hvalue J)

section Translation

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  {P M U Q N W : Subgroup H} [LocallyCompactSpace P] [LocallyCompactSpace Q]
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) (g : K)
  (hP : ∀ x : H, x ∈ Q ↔ (g : H)⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ (g : H)⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ (g : H)⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ N)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Ag" => (conjugationFunctor (g : H) hM).obj A

variable (e : (Ag).representation.Equiv B.representation)
  [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]
  (hA : A.IsAdmissible) (hB : B.IsAdmissible)
  (hcof : CompactOpenCofinal M) (hcof' : CompactOpenCofinal N)
  (b : InvariantPositiveForm A.representation)
  (hPc : IsClosed (P : Set H)) (hQc : IsClosed (Q : Set H))
  (hPK : ∀ g : H, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hQK : ∀ g : H, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (hH : ∀ g : H, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hc P h.le_normalizer q : ℝ≥0))
  (hδ' : ∀ q : Q, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter W hc' Q k.le_normalizer q : ℝ≥0))

set_option hygiene false in
set_option quotPrecheck false in
local notation "L" => CoefficientConjugation.leviCoefficientLeftTranslation
  h k (g : H) hP hM hW hc hc' hu hu' A
set_option hygiene false in
set_option quotPrecheck false in
local notation "C" => coefficientCongr k hc' hu' e
set_option hygiene false in
set_option quotPrecheck false in
local notation "bN" => b.comp (conjugationEquiv (g : H) hM).toMonoidHom
set_option hygiene false in
set_option quotPrecheck false in
local notation "bB" => (bN).ofEquiv e.symm
set_option hygiene false in
set_option quotPrecheck false in
local notation "evA" => Induction.eval (P.prod P) (leviInflatedInducingRepresentation
  (h.prod h) (hc.prod hc) (productLeviObject A A.contragredient))
set_option hygiene false in
set_option quotPrecheck false in
local notation "evB" => Induction.eval (Q.prod Q) (leviInflatedInducingRepresentation
  (k.prod k) (hc'.prod hc') (productLeviObject B B.contragredient))

set_option maxHeartbeats 900000 in
/-- The two original compact probabilities give the same tensor form after
actual left translation by a compact point and the inducing equivalence. -/
theorem leviProductForm_inner_translated
    (F J : leviProductInducedCoefficientObject h hc A) :
    (CompactInduction.leviProductForm k hc' B K hu' hK hQc hQK hH hδ' hB hcof' bB).inner
        ((C) ((L) F)) ((C) ((L) J)) =
      (CompactInduction.leviProductForm h hc A K hu hK hPc hPK hH hδ hA hcof b).inner F J := by
  let : BorelSpace K := inferInstanceAs (BorelSpace (K : Subgroup H))
  let : ContinuousMul K := inferInstanceAs (ContinuousMul (K : Subgroup H))
  let : MeasurableMul K :=
    ⟨fun _ => (continuous_const.mul continuous_id).measurable,
      fun _ => (continuous_id.mul continuous_const).measurable⟩
  let innerA := (coefficientTensorInvariantForm A hcof hA b).inner
  let innerB := (coefficientTensorInvariantForm B hcof' hB bB).inner
  have hAg : (Ag).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (conjugationEquiv (g : H) hM) hA
  have hb : (bB).ofEquiv e = bN := by
    apply InvariantPositiveForm.ext_inner
    intro v w
    exact congrArg₂ (bN).inner (e.symm_apply_apply v) (e.symm_apply_apply w)
  have he (t s : CoefficientTensor Ag) :
      innerB (productCoefficientLeviEquiv e t) (productCoefficientLeviEquiv e s) =
        (coefficientTensorInvariantForm Ag hcof' hAg bN).inner t s := by
    have hform := coefficientTensorInvariantForm_ofEquiv hcof' hAg hB bB e
    rw [hb] at hform
    exact congrArg (fun c => c.inner t s) hform
  let f (x y : K) := innerA (evA F ((x : H), (y : H))) (evA J ((x : H), (y : H)))
  refine (leviProductForm_inner_integral_integral k hc' B K hu' hK hQc hQK hH hδ' hB
    hcof' bB _ _).trans ?_
  refine Eq.trans ?_ (leviProductForm_inner_integral_integral h hc A K hu hK hPc hPK hH hδ
    hA hcof b F J).symm
  calc
    _ = ∫ x : K, ∫ y : K, f (g⁻¹ * x) (g⁻¹ * y)
          ∂CompactInduction.measure K hK ∂CompactInduction.measure K hK := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      have hF := translatedProduct_eval h k (g : H) hP hM hW hc hc' hu hu' A B e F
        ((x : H), (y : H))
      have hJ := translatedProduct_eval h k (g : H) hP hM hW hc hc' hu hu' A B e J
        ((x : H), (y : H))
      refine (congrArg₂ innerB hF hJ).trans ((he _ _).trans ?_)
      exact conjugateValue_inner (g : H) hM A hcof hcof' hA hAg b _ _
    _ = ∫ x : K, ∫ y : K, f (g⁻¹ * x) y
          ∂CompactInduction.measure K hK ∂CompactInduction.measure K hK :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => integral_mul_left_eq_self _ g⁻¹)
    _ = _ := integral_mul_left_eq_self
      (μ := CompactInduction.measure K hK)
      (fun x : K => ∫ y : K, f x y ∂CompactInduction.measure K hK) g⁻¹

/-- For an irreducible target inducing representation, the translated
product form identity holds for every positive form on the target. -/
theorem leviProductForm_inner_translated_of_irreducible
    (hiB : B.representation.IsIrreducible) (c : InvariantPositiveForm B.representation)
    (F J : leviProductInducedCoefficientObject h hc A) :
    (CompactInduction.leviProductForm k hc' B K hu' hK hQc hQK hH hδ' hB hcof' c).inner
        ((C) ((L) F)) ((C) ((L) J)) =
      (CompactInduction.leviProductForm h hc A K hu hK hPc hPK hH hδ hA hcof b).inner F J := by
  rw [CompactInduction.leviProductForm_independent k hc' B K hu' hK hQc hQK hH hδ' hB hcof'
    hiB c bB]
  exact leviProductForm_inner_translated h k K hK g hP hM hW hc hc' hu hu' A B e hA hB
    hcof hcof' b hPc hQc hPK hQK hH hδ hδ' F J

end Translation

end Langlands.Plancherel.TranslatedCoefficientValue
