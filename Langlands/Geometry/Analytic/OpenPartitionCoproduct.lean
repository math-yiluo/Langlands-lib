import Langlands.Geometry.Analytic.OpenPartitionCoproductStatement
import Langlands.Geometry.Analytic.QuotientDomainGluing

/-! # An analytic space partitioned into open domains is their disjoint union -/

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation

namespace SourceCategory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Two morphisms of the source-quotient category out of an empty original-chart domain are
equal. -/
theorem eq_of_carrier_eq_empty (E : A.presentation.atlas.OriginalChartDomain)
    (hE : E.carrier = ∅) (F G : ofPresentation (A.originalDomain E) ⟶ ofPresentation B) :
    F = G := by
  refine eq_of_domainCover (A := A.originalDomain E) (ι := Empty) (fun e => e.elim) ?_ F G
    (fun e => e.elim)
  intro _ _ x _
  let y : E.carrier := x
  exact absurd (hE.subset y.2) (Set.notMem_empty _)

end SourceCategory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {J : Type z} (Y : LocalizedCategory.{u, v, w} (K := K))
  (U : J → Set (presentationOf Y).presentation.space) (hU : ∀ j, IsOpen (U j))

/-- The open domains of a family of open subsets cover the space as soon as the subsets do. -/
theorem locallyRefines_openDomain (hc : ∀ y, ∃ j, y ∈ U j) :
    AtlasTopology.LocallyRefines
      (Set.range fun j => ((presentationOf Y).openDomain (U j) (hU j)).carrier) {Set.univ} := by
  intro W hW x _
  rw [Set.mem_singleton_iff] at hW
  subst hW
  obtain ⟨j, hj⟩ := hc x
  refine ⟨{U j}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · rw [Set.singleton_subset_iff]
    exact ⟨j, rfl⟩
  · intro V hV
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨Set.subset_univ _, hj⟩
  · rw [Set.sUnion_singleton, nhdsWithin_univ]
    exact (hU j).mem_nhds hj

variable (hd : Pairwise fun i j => Disjoint (U i) (U j))

/-- The matching family, in the source-quotient category, of the legs of a cofan over the open
domains of a partition. Overlaps of distinct pieces are empty. -/
def openPartitionMatchingFamily
    (s : Cofan fun j => domainObj Y ((presentationOf Y).openDomain (U j) (hU j))) :
    SourceCategory.QuotientDomainMatchingFamily (presentationOf Y) (presentationOf s.pt)
      (fun j => (presentationOf Y).openDomain (U j) (hU j)) where
  localMap j := SourceCategory.comparisonFunctor.preimage
    (X := SourceCategory.ofPresentation
      ((presentationOf Y).originalDomain ((presentationOf Y).openDomain (U j) (hU j))))
    (Y := SourceCategory.ofPresentation (presentationOf s.pt)) (s.inj j)
  overlap k l := by
    by_cases hkl : k = l
    · subst hkl
      rfl
    · exact SourceCategory.eq_of_carrier_eq_empty _
        (Set.disjoint_iff_inter_eq_empty.1 (hd hkl)) _ _

theorem comparisonFunctor_map_openPartitionMatchingFamily_localMap
    (s : Cofan fun j => domainObj Y ((presentationOf Y).openDomain (U j) (hU j))) (j : J) :
    SourceCategory.comparisonFunctor.map ((openPartitionMatchingFamily Y U hU hd s).localMap j) =
      s.inj j :=
  Functor.map_preimage _ _

/-- An analytic space whose underlying space is partitioned into open subsets is the coproduct
of the corresponding open domains, with their canonical morphisms. -/
def isColimitOpenPartition (hc : ∀ y, ∃ j, y ∈ U j) :
    IsColimit (Cofan.mk Y fun j => domainι Y ((presentationOf Y).openDomain (U j) (hU j))) :=
  Cofan.IsColimit.mk _
    (fun s => SourceCategory.comparisonFunctor.map
      ((openPartitionMatchingFamily Y U hU hd s).glue (locallyRefines_openDomain Y U hU hc)))
    (fun s j => by
      have key := congrArg SourceCategory.comparisonFunctor.map
        ((openPartitionMatchingFamily Y U hU hd s).glue_restrict
          (locallyRefines_openDomain Y U hU hc) j)
      rw [Functor.map_comp, (presentationOf Y).comparisonFunctor_map_domainInclusion,
        comparisonFunctor_map_openPartitionMatchingFamily_localMap] at key
      exact key)
    (fun s m hm => by
      obtain ⟨M, rfl⟩ := (SourceCategory.comparisonFunctor (K := K)).map_surjective
        (X := SourceCategory.ofPresentation (presentationOf Y))
        (Y := SourceCategory.ofPresentation (presentationOf s.pt)) m
      refine congrArg _ (SourceCategory.QuotientDomainMatchingFamily.glue_unique _ _ M
        fun j => SourceCategory.comparisonFunctor.map_injective ?_)
      rw [Functor.map_comp, (presentationOf Y).comparisonFunctor_map_domainInclusion,
        comparisonFunctor_map_openPartitionMatchingFamily_localMap]
      exact hm j)

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- **Open partitions are coproducts.** -/
theorem openPartitionCoproductStatement : OpenPartitionCoproductStatement.{u, v, z} :=
  fun _ _ _ _ _ Y U hU hd hc => ⟨isColimitOpenPartition Y U hU hd hc⟩

end Langlands.Analytic.SaturatedAtlasPresentation
