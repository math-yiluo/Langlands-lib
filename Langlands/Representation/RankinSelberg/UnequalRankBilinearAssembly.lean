import Langlands.Representation.RankinSelberg.UnequalRankBilinearForms
import Mathlib.RingTheory.Length

/-! Actual coefficient-model pullback and conditional unequal-rank descent. -/

noncomputable section

namespace Langlands.RankinSelberg.UnequalRankAssembly

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

section CoefficientModels

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Bilinear pullback along the two actual surjective coefficient-model maps. -/
def coefficientModelBilinearPullback
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    ((coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ) →ₗ[ℂ]
      (V →ₗ[ℂ] W →ₗ[ℂ] ℂ) where
  toFun C := C.compl₁₂ (modelMap π ℓ).toLinearMap (modelMap σ ℓ').toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientModelBilinearPullback_injective
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    Function.Injective (coefficientModelBilinearPullback ψ π σ ℓ ℓ') := by
  intro C D h
  exact (LinearMap.compl₁₂_inj
    (modelMap_surjective π ℓ) (modelMap_surjective σ ℓ')).mp h

/-- Pullback preserves both published covariance laws on the original carriers. -/
theorem coefficientModelBilinearPullback_covariant
    (hnr : n < r) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (s : ℂ)
    (C : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ)
    (hC : IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s C) :
    IsUnequalRankMirabolicCovariant hnr ψ abv
      (π.comp (mirabolic r F).subtype) σ s
      (coefficientModelBilinearPullback ψ π σ ℓ ℓ' C) := by
  constructor
  · intro x v w
    change C (modelMap π ℓ (π (unequalRankEmbedding hnr x).val v))
        (modelMap σ ℓ' (σ x w)) =
      determinantWeight abv x (((r - n : ℕ) : ℂ) / 2 - s) *
        C (modelMap π ℓ v) (modelMap σ ℓ' w)
    rw [(modelMap π ℓ).isIntertwining, (modelMap σ ℓ').isIntertwining]
    exact hC.1 x (modelMap π ℓ v) (modelMap σ ℓ' w)
  · intro u hu v w
    change C (modelMap π ℓ (π u.val v)) (modelMap σ ℓ' w) =
      (standardCharacter ψ r u : ℂ) *
        C (modelMap π ℓ v) (modelMap σ ℓ' w)
    rw [(modelMap π ℓ).isIntertwining]
    exact hC.2 u hu (modelMap π ℓ v) (modelMap σ ℓ' w)

/-- Source-carrier uniqueness descends through the two actual model maps. -/
theorem coefficientModel_uniqueness_of_source
    (hnr : n < r) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (s : ℂ)
    (hsource : ∀ B B' : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
      IsUnequalRankMirabolicCovariant hnr ψ abv
        (π.comp (mirabolic r F).subtype) σ s B →
      IsUnequalRankMirabolicCovariant hnr ψ abv
        (π.comp (mirabolic r F).subtype) σ s B' →
      B ≠ 0 → ∃ c : ℂ, B' = c • B) :
    ∀ B B' : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
        (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ,
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B →
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B' →
      B ≠ 0 → ∃ c : ℂ, B' = c • B := by
  intro B B' hB hB' hB0
  let P := coefficientModelBilinearPullback ψ π σ ℓ ℓ'
  have hinj := coefficientModelBilinearPullback_injective ψ π σ ℓ ℓ'
  have hP0 : P B ≠ 0 := by
    intro hz
    exact hB0 (hinj (hz.trans (map_zero P).symm))
  obtain ⟨c, hc⟩ := hsource (P B) (P B')
    (coefficientModelBilinearPullback_covariant hnr ψ abv π σ ℓ ℓ' s B hB)
    (coefficientModelBilinearPullback_covariant hnr ψ abv π σ ℓ ℓ' s B' hB') hP0
  refine ⟨c, hinj ?_⟩
  rw [map_smul]
  exact hc

end CoefficientModels

section Length

universe uM

private theorem exists_smul_eq_of_submodule_length_le_one
    {M : Type uM} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (h : Module.length ℂ S ≤ 1) (B C : S) (hB : B ≠ 0) :
    ∃ c : ℂ, C = c • B := by
  have hne : Module.length ℂ S ≠ 0 := by
    intro hz
    have hs : Subsingleton S := Module.length_eq_zero_iff.mp hz
    exact hB (hs.elim _ _)
  have hone : Module.length ℂ S = 1 :=
    le_antisymm h (Order.one_le_iff_ne_zero.mpr hne)
  let : IsSimpleModule ℂ S := Module.length_eq_one_iff.mp hone
  have hmem : C ∈ Submodule.span ℂ {B} := by
    rw [IsSimpleModule.span_singleton_eq_top ℂ hB]
    trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

end Length

/-- The exact uniqueness target follows from a uniform bound on the original
carriers. The source length bound remains an explicit hypothesis. -/
theorem unequalRankBilinearUniqueness_of_source_length
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (hsource :
      letI := T.topology
      ∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F.Carrier)
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          Module.length ℂ (unequalRankMirabolicForms hnr ψ
            (normalizedAbsoluteValue T) (π.comp (mirabolic r F.Carrier).subtype) σ s) ≤ 1) :
    UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  intro hnr ψ V _ _ W _ _ π σ hπ hσ ℓ ℓ'
  obtain ⟨E, hE⟩ := hsource hnr ψ V W π σ hπ hσ
  refine ⟨E, ?_⟩
  intro s hs B B' hB hB' hB0
  apply coefficientModel_uniqueness_of_source hnr ψ (normalizedAbsoluteValue T)
    π σ ℓ ℓ' s ?_ B B' hB hB' hB0
  intro C D hC hD hC0
  let C₀ : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
      (π.comp (mirabolic r F.Carrier).subtype) σ s := ⟨C, hC⟩
  let D₀ : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
      (π.comp (mirabolic r F.Carrier).subtype) σ s := ⟨D, hD⟩
  have hC₀ : C₀ ≠ 0 := fun hz => hC0 (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_submodule_length_le_one _ (hE s hs) C₀ D₀ hC₀
  exact ⟨c, congrArg Subtype.val hc⟩

end Langlands.RankinSelberg.UnequalRankAssembly
