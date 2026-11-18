import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.CoefficientTensorFormTransport

/-! # Exact coefficient and form preservation for the common-Levi tensor -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV uW

section CoefficientSimilitude

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {A : SmoothRep.{0, uG, uV} ℂ H} {B : SmoothRep.{0, uG, uW} ℂ H}
  (hcof : CompactOpenCofinal H)
  (hA : IsAdmissible A.representation) (hB : IsAdmissible B.representation)

/-- A positive similarity of representations induces an exact isometry on
coefficient tensors, because vector and actual smooth-dual scalings cancel. -/
theorem coefficientTensorInvariantForm_congr_of_similitude
    (bA : InvariantPositiveForm A.representation)
    (bB : InvariantPositiveForm B.representation)
    (e : A.representation.Equiv B.representation)
    (a : ℝ) (ha : 0 < a) (he : bB.ofEquiv e = bA.rescale a ha) :
    (coefficientTensorInvariantForm B hcof hB bB).ofEquiv
        (coefficientTensorCongrEquiv e) =
      coefficientTensorInvariantForm A hcof hA bA := by
  rw [coefficientTensorInvariantForm_ofEquiv hcof hA hB bB e, he,
    coefficientTensorInvariantForm_rescale]

end CoefficientSimilitude

namespace CompactInduction

open Aubert.General HarishChandraSchwartz

section DegreeNormalization

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] [SecondCountableTopology H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H]
  {P M U : Subgroup H} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup H)
  (huni : IsUnimodularModulus U hU) (hK : IsCompact (K : Set H))
  (hP : IsClosed (P : Set H)) (hm : Continuous h.projection)
  (hPK : ∀ g : H, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hH : ∀ g : H, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hcof : CompactOpenCofinal M) (hcofH : CompactOpenCofinal H)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

/-- Positive-Levi normalization retains the same compact probability duality
and the same inverse formal degree in the coefficient-tensor model. -/
theorem leviFormalDegreeProductForm_eq_coefficientForm
    (b : InvariantPositiveForm A.representation) :
    leviFormalDegreeProductForm h hU A K huni hK hP hPK hH hδ hcof C hC μ hsq hi =
      ((coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
        hcofH (induced_isAdmissible h hU K hK hPK A hm hsq.1)
        (invariantPositiveForm h hU hP K hK hPK hH hδ A b)).ofEquiv
          (leviCoefficientTensorEquiv h hU A K huni hK hP hm hPK hH hδ hsq.1)).rescale
            (representationFormalDegree C hC μ hcof hsq hi)⁻¹
            (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  rw [leviFormalDegreeProductForm_eq h hU A K huni hK hP hPK hH hδ hcof C hC μ hsq hi b,
    leviProductForm_eq_coefficientForm h hU A K huni hK hP hm hPK hH hδ hsq.1
      hcof hcofH b]

end DegreeNormalization

section Comparison

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] [SecondCountableTopology H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H]
  {P₀ P₁ M U₀ U₁ : Subgroup H}
  [LocallyCompactSpace P₀] [LocallyCompactSpace P₁]
  (h₀ : IsSemidirectDecomposition P₀ M U₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁)
  (hU₀ : IsClosed (U₀ : Set H)) (hU₁ : IsClosed (U₁ : Set H))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup H)
  (huni₀ : IsUnimodularModulus U₀ hU₀) (huni₁ : IsUnimodularModulus U₁ hU₁)
  (hK : IsCompact (K : Set H))
  (hP₀ : IsClosed (P₀ : Set H)) (hP₁ : IsClosed (P₁ : Set H))
  (hm₀ : Continuous h₀.projection) (hm₁ : Continuous h₁.projection)
  (hPK₀ : ∀ g : H, ∃ q ∈ P₀, ∃ k ∈ K, g = q * k)
  (hPK₁ : ∀ g : H, ∃ q ∈ P₁, ∃ k ∈ K, g = q * k)
  (hH : ∀ g : H, Measure.modularCharacter g = 1)
  (hδ₀ : ∀ q : P₀, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U₀ hU₀ P₀ h₀.le_normalizer q : ℝ≥0))
  (hδ₁ : ∀ q : P₁, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U₁ hU₁ P₁ h₁.le_normalizer q : ℝ≥0))
  (hcof : CompactOpenCofinal M) (hcofH : CompactOpenCofinal H)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

set_option quotPrecheck false in
local notation "I₀" => (normalizedInductionFunctor h₀ hU₀).obj A
set_option quotPrecheck false in
local notation "I₁" => (normalizedInductionFunctor h₁ hU₁).obj A
set_option quotPrecheck false in
local notation "E₀" => leviCoefficientTensorEquiv h₀ hU₀ A K huni₀ hK hP₀ hm₀ hPK₀ hH hδ₀ hsq.1
set_option quotPrecheck false in
local notation "E₁" => leviCoefficientTensorEquiv h₁ hU₁ A K huni₁ hK hP₁ hm₁ hPK₁ hH hδ₁ hsq.1
set_option quotPrecheck false in
local notation "B₀" b => invariantPositiveForm h₀ hU₀ hP₀ K hK hPK₀ hH hδ₀ A b
set_option quotPrecheck false in
local notation "B₁" b => invariantPositiveForm h₁ hU₁ hP₁ K hK hPK₁ hH hδ₁ A b

/-- The actual positive-Levi coefficient equivalence induced by a normalized
induction equivalence and its smooth-dual coefficient transport. -/
def leviCoefficientCongrEquiv
    (e : (I₀).representation.Equiv (I₁).representation) :
    (leviProductInducedCoefficientObject h₀ hU₀ A).representation.Equiv
      (leviProductInducedCoefficientObject h₁ hU₁ A).representation :=
  (E₀).trans ((coefficientTensorCongrEquiv e).trans (E₁).symm)

omit [BorelSpace (M ⧸ C)] [μ.IsInvInvariant] in
/-- The constructed coefficient equivalence has the canonical tensor square
on every coefficient vector. -/
theorem leviCoefficientCongrEquiv_square
    (e : (I₀).representation.Equiv (I₁).representation)
    (v : leviProductInducedCoefficientObject h₀ hU₀ A) :
    E₁ (leviCoefficientCongrEquiv h₀ h₁ hU₀ hU₁ A K huni₀ huni₁ hK
      hP₀ hP₁ hm₀ hm₁ hPK₀ hPK₁ hH hδ₀ hδ₁ C hC μ hsq e v) =
      coefficientTensorCongr e (E₀ v) := by
  exact (E₁).apply_symm_apply _

include hcofH in
/-- An actual product-group intertwiner whose coefficient-tensor square is a
positive similarity preserves every coefficient and the exact source form.
Only the inducing representation is assumed irreducible. -/
theorem levi_preserves_of_coefficientTensor_similitude
    (T : (leviProductInducedCoefficientObject h₀ hU₀ A).representation.IntertwiningMap
      (leviProductInducedCoefficientObject h₁ hU₁ A).representation)
    (e : (I₀).representation.Equiv (I₁).representation)
    (b : InvariantPositiveForm A.representation)
    (a : ℝ) (ha : 0 < a)
    (hsquare : ∀ v, E₁ (T v) = coefficientTensorCongr e (E₀ v))
    (hsim : (B₁ b).ofEquiv e = (B₀ b).rescale a ha) :
    Function.Bijective T ∧
      (∀ v, leviCoefficientMap h₁ hU₁ A K huni₁ hK hP₁ hm₁ hPK₁ hH hδ₁ hsq.1 (T v) =
        leviCoefficientMap h₀ hU₀ A K huni₀ hK hP₀ hm₀ hPK₀ hH hδ₀ hsq.1 v) ∧
      ∀ v w,
        (leviFormalDegreeProductForm h₁ hU₁ A K huni₁ hK hP₁ hPK₁ hH hδ₁
          hcof C hC μ hsq hi).inner (T v) (T w) =
        (leviFormalDegreeProductForm h₀ hU₀ A K huni₀ hK hP₀ hPK₀ hH hδ₀
          hcof C hC μ hsq hi).inner v w := by
  have ht : (T : _ → _) = fun v => (E₁).symm (coefficientTensorCongr e (E₀ v)) := by
    funext v
    exact ((E₁).symm_apply_apply (T v)).symm.trans (congrArg (E₁).symm (hsquare v))
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact (E₁).symm.bijective.comp ((coefficientTensorCongr e).bijective.comp (E₀).bijective)
  · intro v
    change coefficientTensorMap I₁ (E₁ (T v)) = coefficientTensorMap I₀ (E₀ v)
    rw [hsquare]
    exact coefficientTensorMap_congr e (E₀ v)
  · intro v w
    have hform := coefficientTensorInvariantForm_congr_of_similitude hcofH
      (induced_isAdmissible h₀ hU₀ K hK hPK₀ A hm₀ hsq.1)
      (induced_isAdmissible h₁ hU₁ K hK hPK₁ A hm₁ hsq.1)
      (B₀ b) (B₁ b) e a ha hsim
    have hin := congrArg (fun c => c.inner (E₀ v) (E₀ w)) hform
    change (coefficientTensorInvariantForm I₁ hcofH _ (B₁ b)).inner
        (coefficientTensorCongr e (E₀ v)) (coefficientTensorCongr e (E₀ w)) =
      (coefficientTensorInvariantForm I₀ hcofH _ (B₀ b)).inner (E₀ v) (E₀ w) at hin
    rw [leviFormalDegreeProductForm_eq_coefficientForm h₁ hU₁ A K huni₁ hK hP₁ hm₁
      hPK₁ hH hδ₁ hcof hcofH C hC μ hsq hi b,
      leviFormalDegreeProductForm_eq_coefficientForm h₀ hU₀ A K huni₀ hK hP₀ hm₀
        hPK₀ hH hδ₀ hcof hcofH C hC μ hsq hi b]
    change _ * (coefficientTensorInvariantForm I₁ hcofH _ (B₁ b)).inner
        (E₁ (T v)) (E₁ (T w)) =
      _ * (coefficientTensorInvariantForm I₀ hcofH _ (B₀ b)).inner (E₀ v) (E₀ w)
    rw [hsquare, hsquare, hin]

end Comparison

end CompactInduction
end Langlands.Plancherel
