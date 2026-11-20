import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLReduction
import Langlands.Representation.Archimedean.RealGenericStandardUnitaryClassificationStatement
import Langlands.Representation.Archimedean.RealStandardParameterUnitary

/-! # Deduction of the real exponent bound from classification and uniqueness -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

universe uV

private theorem exponent_of_mem_normalize {x y : RealBlock} (h : y ∈ realBlockNormalize x) :
    realBlockExponent y = realBlockExponent x := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  have hpos : realBlockExponent a.positiveWeight = realBlockExponent a := by
    cases a with
    | character _ => rfl
    | induced d =>
      by_cases hneg : d.weight < 0 <;>
        simp [RealBlock.positiveWeight, hneg, realBlockExponent, ComplexCharacterData.conj]
  exact hpos.trans (realBlockExponent_of_mem_expand ha)

private theorem exists_mem_normalize (x : RealBlock) : ∃ y, y ∈ realBlockNormalize x := by
  cases x with
  | character c => exact ⟨.character c, by simp [realBlockNormalize, realBlockExpand,
      RealBlock.positiveWeight]⟩
  | induced d =>
    by_cases hw : d.weight = 0
    · simp [realBlockNormalize, realBlockExpand, hw]
    · simp [realBlockNormalize, realBlockExpand, hw]

private theorem irreducible_of_standard_injection {n : ℕ} {ds es : List RealBlock}
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hgen : IsRealGenericGKModule n (realStandardLie n ds))
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds))
    (hrank : realRank es = n) (h : RealInjectiveIntertwinerExists n es ds) :
    IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) := by
  obtain ⟨T, hTi, hT⟩ := h
  have hparam : HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es :=
    ⟨hrank, T, hTi, hT⟩
  exact (realStandardParameter_model hirr hgen hunit hparam).2.1

/-- The generic unitary classification and uniqueness of positive-weight real standard
parameters imply the strict exponent bound. -/
def RealUnitaryGenericExponentBoundClassificationReductionStatement : Prop :=
  RealGenericStandardUnitaryClassificationStatement →
    RealPositiveWeightStandardUniqueStatement → RealUnitaryGenericExponentBoundStatement.{uV}

theorem realUnitaryGenericExponentBound_of_classification :
    RealUnitaryGenericExponentBoundClassificationReductionStatement.{uV} := by
  intro hclass hunique
  apply realUnitaryGenericExponentBound_of_standard
  intro n ds hrank hirr hgen hunit x hx
  obtain ⟨es, hdata, heRank, A, hAi, hA⟩ := hclass n ds hrank hirr hunit
  have hdM := realStandardModule_flatMap_normalize n ds
  have heM := realStandardModule_flatMap_normalize n es
  have hdRank := (realRank_flatMap_normalize ds).trans hrank
  have heRank' := (realRank_flatMap_normalize es).trans heRank
  have hE : RealInjectiveIntertwinerExists n es ds := ⟨A, hAi, hA⟩
  have hD : RealInjectiveIntertwinerExists n ds ds :=
    ⟨LinearMap.id, fun _ _ h => h, isRealStandardIntertwiner_id n ds⟩
  have hdI := irreducible_of_standard_injection hirr hgen hunit hdRank
    (hD.of_eq hdM.symm rfl)
  have heI := irreducible_of_standard_injection hirr hgen hunit heRank'
    (hE.of_eq heM.symm rfl)
  obtain ⟨T, hTi, hT⟩ := hE.of_eq heM.symm hdM.symm
  have hT0 : T ≠ 0 := by
    let hnt := heI.1
    obtain ⟨v, hv⟩ := exists_ne (0 : kFiniteFunctions
      (realStandardModule n (es.flatMap realBlockNormalize)) (unitaryCompact ℝ n))
    intro hzero
    exact hv (hTi (by simp [hzero]))
  have hperm := hunique n _ _ heRank' hdRank
    (fun _ => weight_pos_of_mem_flatMap_normalize) (fun _ => weight_pos_of_mem_flatMap_normalize)
    heI hdI T hT ⟨hTi, hT.surjective hdI hT0⟩
  obtain ⟨y, hy⟩ := exists_mem_normalize x
  have hy' := hperm.mem_iff.mpr (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy'
  rw [← exponent_of_mem_normalize hy, exponent_of_mem_normalize hyz]
  exact hdata.exponent_bound hz

end Langlands.Archimedean
