import Langlands.Cohomology.Continuous.FiniteStageExactnessLimitStatement
import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof
import Langlands.Cohomology.Continuous.RestrictionComparisonProof
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G]

set_option backward.isDefEq.respectTransparency false in
/-- Every continuous class is the image of an actual finite-stage class. -/
theorem finiteStageToContinuous_jointly_surjective (A : DiscreteModule k G) (q : ℕ)
    (x : continuousCohomology q A.toTopRep) :
    ∃ (N : OpenNormalSubgroup G) (y : groupCohomology (finiteQuotientRep A.toRep N) q),
      finiteStageToContinuous A N q y = x := by
  obtain ⟨N, y, hy⟩ := Limits.Concrete.colimit_exists_rep
    (finiteQuotientDiagram A.toRep q) ((finiteQuotientComparisonIso A q).inv x)
  refine ⟨OrderDual.ofDual N, y, ?_⟩
  have h := ConcreteCategory.congr_hom
    (finiteStageToColimit_comp_comparison A (OrderDual.ofDual N) q) y
  change finiteQuotientComparison A q (finiteStageToColimit A.toRep (OrderDual.ofDual N) q y) = _ at h
  rw [← h]
  change finiteQuotientComparison A q (Limits.colimit.ι (finiteQuotientDiagram A.toRep q) N y) = x
  rw [hy]
  exact ConcreteCategory.congr_hom (finiteQuotientComparisonIso A q).inv_hom_id x

set_option backward.isDefEq.respectTransparency false in
/-- A finite-stage class killed continuously becomes zero at a smaller open normal subgroup. -/
theorem finiteStageToContinuous_eventually_zero (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ)
    (y : groupCohomology (finiteQuotientRep A.toRep N) q)
    (hy : finiteStageToContinuous A N q y = 0) :
    ∃ (M : OpenNormalSubgroup G) (h : M ≤ N), finiteInflation A.toRep q h y = 0 := by
  have hz : finiteStageToColimit A.toRep N q y =
      finiteStageToColimit A.toRep N q 0 := by
    apply (ModuleCat.mono_iff_injective (finiteQuotientComparison A q)).mp inferInstance
    have h := ConcreteCategory.congr_hom (finiteStageToColimit_comp_comparison A N q) y
    change finiteQuotientComparison A q (finiteStageToColimit A.toRep N q y) = _ at h
    rw [h, hy, map_zero, map_zero]
  obtain ⟨M, f, g, hfg⟩ := Limits.Concrete.colimit_exists_of_rep_eq
    (finiteQuotientDiagram A.toRep q)
    (i := OrderDual.toDual N) (j := OrderDual.toDual N) y 0 hz
  refine ⟨OrderDual.ofDual M, leOfHom f, ?_⟩
  rw [map_zero] at hfg
  simpa [finiteQuotientDiagram, finiteQuotientCochainDiagram, finiteInflation,
    groupCohomology.map, groupCohomology, HomologicalComplex.homologyFunctor] using hfg

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] [IsTopologicalGroup G] [CompactSpace G] [LocallyCompactSpace G] in
/-- Inflation along the identity refinement is the identity map. -/
theorem finiteInflation_refl (A : Rep.{u} k G) (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteInflation A q (le_refl N) = 𝟙 _ := by
  simpa [finiteQuotientDiagram, finiteQuotientCochainDiagram, finiteInflation,
    groupCohomology.map, groupCohomology, HomologicalComplex.homologyFunctor] using
    (finiteQuotientDiagram A q).map_id (OrderDual.toDual N)

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] [IsTopologicalGroup G] [CompactSpace G] [LocallyCompactSpace G] in
/-- Finite-stage inflation composes along subgroup refinement. -/
theorem finiteInflation_trans (A : Rep.{u} k G) {L M N : OpenNormalSubgroup G}
    (hLM : L ≤ M) (hMN : M ≤ N) (q : ℕ) :
    finiteInflation A q hMN ≫ finiteInflation A q hLM =
      finiteInflation A q (hLM.trans hMN) := by
  simpa [finiteQuotientDiagram, finiteQuotientCochainDiagram, finiteInflation,
    groupCohomology.map] using
    ((finiteQuotientDiagram A q).map_comp
      (homOfLE (show OrderDual.toDual N ≤ OrderDual.toDual M from hMN))
      (homOfLE (show OrderDual.toDual M ≤ OrderDual.toDual L from hLM))).symm

set_option backward.isDefEq.respectTransparency false in
/-- Finite exactness implies injectivity and exactness for the actual continuous maps. -/
theorem finiteStageExactnessLimit : FiniteStageExactnessLimit.{u} := by
  intro k G _ _ _ _ _ _ _ A H q hfinite
  let : CompactSpace H.toSubgroup :=
    isCompact_iff_compactSpace.mp H.toOpenSubgroup.isClosed.isCompact
  have hinj : Function.Injective (finiteStageToContinuous A H q) := by
    intro x y hxy
    have hz : finiteStageToContinuous A H q (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨M, hMH, hM⟩ := finiteStageToContinuous_eventually_zero A H q (x - y) hz
    apply sub_eq_zero.mp
    apply (hfinite M hMH).1
    simpa only [map_zero] using hM
  refine ⟨hinj, le_antisymm ?_ ?_⟩
  · rintro x ⟨y, rfl⟩
    have hy : finiteRestriction A H.toOpenSubgroup H q y = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← (hfinite H le_rfl).2]
      refine ⟨y, ?_⟩
      exact ConcreteCategory.congr_hom (finiteInflation_refl A.toRep H q) y
    apply LinearMap.mem_ker.mpr
    have h := ConcreteCategory.congr_hom
      (finiteRestriction_comp_stage A H.toOpenSubgroup H q) y
    change finiteStageToContinuous (A.restrict H.toSubgroup)
        (restrictOpenNormal H.toOpenSubgroup H) q
        (finiteRestriction A H.toOpenSubgroup H q y) =
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (continuousRestriction A H.toSubgroup q)) (finiteStageToContinuous A H q y) at h
    simpa only [hy, map_zero] using h.symm
  · intro x hx
    obtain ⟨N, y, hy⟩ := finiteStageToContinuous_jointly_surjective A q x
    have hz : finiteStageToContinuous (A.restrict H.toSubgroup)
        (restrictOpenNormal H.toOpenSubgroup N) q
        (finiteRestriction A H.toOpenSubgroup N q y) = 0 := by
      have h := ConcreteCategory.congr_hom
        (finiteRestriction_comp_stage A H.toOpenSubgroup N q) y
      change finiteStageToContinuous (A.restrict H.toSubgroup)
          (restrictOpenNormal H.toOpenSubgroup N) q
          (finiteRestriction A H.toOpenSubgroup N q y) =
        ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousRestriction A H.toSubgroup q)) (finiteStageToContinuous A N q y) at h
      rw [h, hy]
      exact LinearMap.mem_ker.mp hx
    obtain ⟨P, hPN, hP⟩ := finiteStageToContinuous_eventually_zero
      (A.restrict H.toSubgroup) (restrictOpenNormal H.toOpenSubgroup N) q
      (finiteRestriction A H.toOpenSubgroup N q y) hz
    obtain ⟨M, hMH, hMP⟩ := exists_ambient_openNormal H.toOpenSubgroup P
    let L : OpenNormalSubgroup G := M ⊓ N
    have hLN : L ≤ N := inf_le_right
    have hLH : L ≤ H := (show L ≤ M from inf_le_left).trans hMH
    have hLP : restrictOpenNormal H.toOpenSubgroup L ≤ P :=
      (restrictOpenNormal_le H.toOpenSubgroup (show L ≤ M from inf_le_left)).trans hMP
    let z := finiteInflation A.toRep q hLN y
    have hzL : finiteRestriction A H.toOpenSubgroup L q z = 0 := by
      have ht := ConcreteCategory.congr_hom
        (finiteInflation_trans (A.restrict H.toSubgroup).toRep hLP hPN q)
        (finiteRestriction A H.toOpenSubgroup N q y)
      have hr := ConcreteCategory.congr_hom
        (finiteRestriction_refinement A H.toOpenSubgroup hLN q) y
      change finiteInflation (A.restrict H.toSubgroup).toRep q
          (restrictOpenNormal_le H.toOpenSubgroup hLN)
          (finiteRestriction A H.toOpenSubgroup N q y) =
        finiteRestriction A H.toOpenSubgroup L q z at hr
      rw [← hr]
      change finiteInflation (A.restrict H.toSubgroup).toRep q hLP
          (finiteInflation (A.restrict H.toSubgroup).toRep q hPN
            (finiteRestriction A H.toOpenSubgroup N q y)) = _ at ht
      rw [hP, map_zero] at ht
      exact ht.symm
    have hzrange : z ∈ LinearMap.range (finiteInflation A.toRep q hLH).hom := by
      rw [(hfinite L hLH).2]
      exact LinearMap.mem_ker.mpr hzL
    obtain ⟨w, hw⟩ := hzrange
    refine ⟨w, ?_⟩
    have hwc := ConcreteCategory.congr_hom (finiteStageToContinuous_refinement A hLH q) w
    have hyc := ConcreteCategory.congr_hom (finiteStageToContinuous_refinement A hLN q) y
    change finiteStageToContinuous A L q (finiteInflation A.toRep q hLH w) =
      finiteStageToContinuous A H q w at hwc
    change finiteStageToContinuous A L q z = finiteStageToContinuous A N q y at hyc
    rw [← hwc, hw, hyc, hy]

end Langlands.Continuous
