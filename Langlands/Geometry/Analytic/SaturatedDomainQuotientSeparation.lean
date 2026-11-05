import Langlands.Geometry.Analytic.SaturatedDomainCorestriction
import Langlands.Geometry.Analytic.OriginalDomainCoverSelection

/-! # Quotient equality of full strong maps over original-domain covers -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter
open AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Categorical restriction along the actual source inclusion retains every
bounded pullback of the literal strong source restriction. -/
theorem refiningSubatlasInclusion_comp_eq_restrictSubatlasSource
    (P : A.presentation.atlas.RefiningSelection) (f : A ⟶ B) :
    A.refiningSubatlasInclusion P ≫ f =
      f.restrictSubatlasSource P.carrier P.locally_refining := by
  refine StrongHom.ext_of_saturated
    (A.refiningSubpresentation P).hasAllLocalDomains rfl ?_
  intro i
  obtain ⟨j, hj⟩ := f.target_exists i.val
  have hi : (A.refiningSubatlasInclusion P).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨j, hj, ?_⟩
  refine (StrongHom.saturatedComp_pullback (A.refiningSubatlasInclusion P) f
    (A.refiningSubpresentation P).hasAllLocalDomains A.hasAllLocalDomains
    i i.val j hi hj hj).trans ?_
  change (A.presentation.atlas.restriction i.val i.val _).comp
    (f.pullback i.val j hj) = f.pullback i.val j hj
  rw [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- Equality of original strong maps in the actual source quotient is exactly
full equality after some original-chart source selection. -/
theorem strongFunctor_map_eq_iff_exists_refiningRestriction (f g : A ⟶ B) :
    SourceCategory.strongFunctor.map f = SourceCategory.strongFunctor.map g ↔
      ∃ P : A.presentation.atlas.RefiningSelection,
        f.restrictSubatlasSource P.carrier P.locally_refining =
          g.restrictSubatlasSource P.carrier P.locally_refining := by
  constructor
  · intro h
    erw [SourceCategory.strongFunctor_map_eq_ι ⊤ f,
      SourceCategory.strongFunctor_map_eq_ι ⊤ g, sourceHomι_eq_iff] at h
    obtain ⟨P, hP, hP', heq⟩ := h
    unfold refiningHomRestriction at heq
    rw [← Category.assoc, ← Category.assoc, refiningSubatlasMap_inclusion] at heq
    rw [refiningSubatlasInclusion_comp_eq_restrictSubatlasSource,
      refiningSubatlasInclusion_comp_eq_restrictSubatlasSource] at heq
    exact ⟨P, heq⟩
  · rintro ⟨P, h⟩
    rw [SourceCategory.strongFunctor_map_eq_ι P f,
      SourceCategory.strongFunctor_map_eq_ι P g,
      refiningSubatlasInclusion_comp_eq_restrictSubatlasSource,
      refiningSubatlasInclusion_comp_eq_restrictSubatlasSource, h]

variable {ι : Type z} (f g : A ⟶ B)
  (D : ι → A.presentation.atlas.OriginalChartDomain)

/-- Equality in the actual source quotient on every original-domain subspace. -/
def StrongLocallyEqualOnDomains : Prop :=
  ∀ k, SourceCategory.strongFunctor.map (X := A.originalDomain (D k)) (Y := B)
      (f.restrictSubspace (D k).carrier (D k).is_domain :
        A.originalDomain (D k) ⟶ B) =
    SourceCategory.strongFunctor.map (X := A.originalDomain (D k)) (Y := B)
      (g.restrictSubspace (D k).carrier (D k).is_domain :
        A.originalDomain (D k) ⟶ B)

/-- Choose a genuine local source selection witnessing the supplied quotient
equality, using the proved equality criterion. -/
def domainEqualityLocalSelection (h : StrongLocallyEqualOnDomains f g D) (k : ι) :
    (A.originalDomain (D k)).presentation.atlas.RefiningSelection :=
  Classical.choose ((strongFunctor_map_eq_iff_exists_refiningRestriction
    (A := A.originalDomain (D k)) (B := B)
    (f.restrictSubspace (D k).carrier (D k).is_domain :
      A.originalDomain (D k) ⟶ B)
    (g.restrictSubspace (D k).carrier (D k).is_domain :
      A.originalDomain (D k) ⟶ B)).mp (h k))

theorem domainEqualityLocalSelection_eq
    (h : StrongLocallyEqualOnDomains f g D) (k : ι) :
    (f.restrictSubspace (D k).carrier (D k).is_domain).restrictSubatlasSource
        (domainEqualityLocalSelection f g D h k).carrier
        (domainEqualityLocalSelection f g D h k).locally_refining =
      (g.restrictSubspace (D k).carrier (D k).is_domain).restrictSubatlasSource
        (domainEqualityLocalSelection f g D h k).carrier
        (domainEqualityLocalSelection f g D h k).locally_refining :=
  Classical.choose_spec ((strongFunctor_map_eq_iff_exists_refiningRestriction
    (A := A.originalDomain (D k)) (B := B)
    (f.restrictSubspace (D k).carrier (D k).is_domain :
      A.originalDomain (D k) ⟶ B)
    (g.restrictSubspace (D k).carrier (D k).is_domain :
      A.originalDomain (D k) ⟶ B)).mp (h k))

variable (hD : AtlasTopology.LocallyRefines
  (Set.range (fun k => (D k).carrier)) {Set.univ})

/-- Construct a global original-chart selection from the local quotient
equality witnesses over the actual quasinet domain cover. -/
def domainCoverEqualitySelection (h : StrongLocallyEqualOnDomains f g D) :
    A.presentation.atlas.RefiningSelection :=
  IndexedAffinoidAtlas.coverRefiningSelection D
    (domainEqualityLocalSelection f g D h) hD

include hD in
/-- The local witnesses also determine equality of the actual continuous maps. -/
theorem baseMap_eq_of_strongLocallyEqualOnDomains
    (h : StrongLocallyEqualOnDomains f g D) : f.baseMap = g.baseMap := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨σ, _hf, hs, _hm, hn⟩ :=
    hD Set.univ (Set.mem_singleton _) x (Set.mem_univ _)
  have hx : x ∈ ⋃₀ σ := mem_of_mem_nhds
    (by simpa only [nhdsWithin_univ] using hn)
  obtain ⟨V, hV, hxV⟩ := hx
  obtain ⟨k, rfl⟩ := hs hV
  exact congrArg
    (fun q => q.baseMap (⟨x, hxV⟩ : (D k).carrier))
    (domainEqualityLocalSelection_eq f g D h k)

/-- Every selected original chart retains equality of the complete bounded
pullbacks from one local source-selection witness. -/
theorem domainCoverEqualitySelection_eq
    (h : StrongLocallyEqualOnDomains f g D) :
    f.restrictSubatlasSource (domainCoverEqualitySelection f g D hD h).carrier
        (domainCoverEqualitySelection f g D hD h).locally_refining =
      g.restrictSubatlasSource (domainCoverEqualitySelection f g D hD h).carrier
        (domainCoverEqualitySelection f g D hD h).locally_refining := by
  refine StrongHom.ext_of_pullback
    (baseMap_eq_of_strongLocallyEqualOnDomains f g D hD h) ?_
  intro i j hf hg
  obtain ⟨k, hi, hR⟩ := i.property
  let c : A.presentation.atlas.SubspaceChart (D k).carrier := ⟨i.val, hi⟩
  let cR : ((A.originalDomain (D k)).refiningSubpresentation
      (domainEqualityLocalSelection f g D h k)).presentation.atlas.Index := ⟨c, hR⟩
  exact StrongHom.pullback_congr (domainEqualityLocalSelection_eq f g D h k)
    cR j
    ((f.restrictSubspace_admissible_iff (D k).carrier (D k).is_domain c j).mpr hf)
    ((g.restrictSubspace_admissible_iff (D k).carrier (D k).is_domain c j).mpr hg)

include hD in
/-- Local quotient equality over any actual original-domain quasinet cover
implies global equality in the source quotient for original full strong maps. -/
theorem strongFunctor_map_eq_of_domainCover
    (h : StrongLocallyEqualOnDomains f g D) :
    SourceCategory.strongFunctor.map f = SourceCategory.strongFunctor.map g :=
  (strongFunctor_map_eq_iff_exists_refiningRestriction f g).mpr
    ⟨domainCoverEqualitySelection f g D hD h,
      domainCoverEqualitySelection_eq f g D hD h⟩

end Langlands.Analytic.SaturatedAtlasPresentation
