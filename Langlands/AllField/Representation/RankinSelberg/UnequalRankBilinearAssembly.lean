import Langlands.Representation.RankinSelberg.UnequalRankBilinearAssembly
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-! Actual coefficient-model pullback and conditional unequal-rank descent. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.UnequalRankAssembly
open Langlands.RankinSelberg.UnequalRankAssembly hiding unequalRankBilinearUniqueness_of_source_length
open Langlands.AllField.RankinSelberg.UnequalRankAssembly
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

section CoefficientModels

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

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
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ)
    (hsource :
      letI := T.topology
      ∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F)
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          Module.length ℂ (unequalRankMirabolicForms hnr ψ
            (normalizedAbsoluteValue T) (π.comp (mirabolic r F).subtype) σ s) ≤ 1) :
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
      (π.comp (mirabolic r F).subtype) σ s := ⟨C, hC⟩
  let D₀ : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
      (π.comp (mirabolic r F).subtype) σ s := ⟨D, hD⟩
  have hC₀ : C₀ ≠ 0 := fun hz => hC0 (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_submodule_length_le_one _ (hE s hs) C₀ D₀ hC₀
  exact ⟨c, congrArg Subtype.val hc⟩

end Langlands.AllField.RankinSelberg.UnequalRankAssembly
