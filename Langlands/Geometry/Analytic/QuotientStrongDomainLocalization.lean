import Langlands.Geometry.Analytic.QuotientChartRepresentatives
import Langlands.Geometry.Analytic.SaturatedDomainHomLocalization
import Langlands.Geometry.Analytic.OriginalDomainStrongLocalization

/-! # Full strong nested-domain comparisons and their quotient images -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Insert intermediate domain membership while retaining every original
bounded restriction, by transporting the full identity map. -/
def nestedDomainStrongMap (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    A.originalDomain (S.subspaceExtend U) ⟶ (A.originalDomain S).originalDomain U :=
  StrongHom.fromNestedOriginalDomain (A := A.presentation) S U
    (StrongHom.id ((A.originalDomain S).originalDomain U).presentation)

/-- Forget intermediate domain membership, retaining all bounded maps. -/
def nestedDomainStrongInverse (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    (A.originalDomain S).originalDomain U ⟶ A.originalDomain (S.subspaceExtend U) :=
  StrongHom.toNestedOriginalDomain (A := A.presentation) S U
    (StrongHom.id (A.originalDomain (S.subspaceExtend U)).presentation)

/-- Composition with the full forward comparison is exactly the published
transport of every bounded map from the nested presentation. -/
theorem nestedDomainStrongMap_comp (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (f : (A.originalDomain S).originalDomain U ⟶ B) :
    (nestedDomainStrongMap S U ≫ f : A.originalDomain (S.subspaceExtend U) ⟶ B) =
      StrongHom.fromNestedOriginalDomain (A := A.presentation) (B := B.presentation)
        S U f := by
  refine StrongHom.ext_of_saturated
    (A.originalDomain (S.subspaceExtend U)).hasAllLocalDomains rfl ?_
  intro c
  let d : ((A.originalDomain S).originalDomain U).presentation.atlas.Index :=
    S.subspaceExtendChartEquiv U c
  obtain ⟨j, hf⟩ := f.target_exists d
  have hc : (nestedDomainStrongMap (A := A) S U).baseMap ''
      Set.range ((A.originalDomain (S.subspaceExtend U)).presentation.atlas.chart c) ⊆
        Set.range (((A.originalDomain S).originalDomain U).presentation.atlas.chart d) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hcomp := (nestedDomainStrongMap S U).comp_admissible f c d j hc hf
  refine ⟨j, hcomp, ?_⟩
  refine (StrongHom.saturatedComp_pullback (nestedDomainStrongMap S U) f
    (A.originalDomain (S.subspaceExtend U)).hasAllLocalDomains
    ((A.originalDomain S).originalDomain U).hasAllLocalDomains c d j hc hf hcomp).trans ?_
  change (((A.originalDomain S).originalDomain U).presentation.atlas.restriction d d
    (Set.Subset.refl _)).comp
    (f.pullback d j hf) = f.pullback d j _
  simp only [IndexedAffinoidAtlas.restriction_id, BoundedAlgHom.id_comp]

/-- Composition with the inverse comparison is exactly the full reverse
transport, rather than just its continuous point map. -/
theorem nestedDomainStrongInverse_comp (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (f : A.originalDomain (S.subspaceExtend U) ⟶ B) :
    (nestedDomainStrongInverse S U ≫ f : (A.originalDomain S).originalDomain U ⟶ B) =
      StrongHom.toNestedOriginalDomain (A := A.presentation) (B := B.presentation)
        S U f := by
  refine StrongHom.ext_of_saturated
    ((A.originalDomain S).originalDomain U).hasAllLocalDomains rfl ?_
  intro c
  let d : (A.originalDomain (S.subspaceExtend U)).presentation.atlas.Index :=
    (S.subspaceExtendChartEquiv U).symm c
  obtain ⟨j, hf⟩ := f.target_exists d
  have hc : (nestedDomainStrongInverse (A := A) S U).baseMap ''
      Set.range (((A.originalDomain S).originalDomain U).presentation.atlas.chart c) ⊆
        Set.range ((A.originalDomain (S.subspaceExtend U)).presentation.atlas.chart d) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hcomp := (nestedDomainStrongInverse S U).comp_admissible f c d j hc hf
  refine ⟨j, hcomp, ?_⟩
  refine (StrongHom.saturatedComp_pullback (nestedDomainStrongInverse S U) f
    ((A.originalDomain S).originalDomain U).hasAllLocalDomains
    (A.originalDomain (S.subspaceExtend U)).hasAllLocalDomains c d j hc hf hcomp).trans ?_
  change ((A.originalDomain (S.subspaceExtend U)).presentation.atlas.restriction d d
    (Set.Subset.refl _)).comp
    (f.pullback d j hf) = f.pullback d j _
  simp only [IndexedAffinoidAtlas.restriction_id, BoundedAlgHom.id_comp]

/-- The full forward comparison commutes with inclusion into the intermediate
domain, including the complete family of admissible bounded pullbacks. -/
theorem nestedDomainStrongMap_inclusion (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    (nestedDomainStrongMap S U ≫ (A.originalDomain S).originalDomainInclusion U :
        A.originalDomain (S.subspaceExtend U) ⟶ A.originalDomain S) =
      A.presentation.originalDomainStrongMap (S.subspaceExtend_le U) := by
  erw [nestedDomainStrongMap_comp]
  refine StrongHom.ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- The ambient-image domain and its nested presentation are actually
isomorphic already in the full strong category. -/
def nestedDomainStrongIso (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    A.originalDomain (S.subspaceExtend U) ≅ (A.originalDomain S).originalDomain U where
  hom := nestedDomainStrongMap S U
  inv := nestedDomainStrongInverse S U
  hom_inv_id := by
    erw [nestedDomainStrongMap_comp]
    exact StrongHom.fromNestedOriginalDomain_toNestedOriginalDomain S U _
  inv_hom_id := by
    erw [nestedDomainStrongInverse_comp]
    exact StrongHom.toNestedOriginalDomain_fromNestedOriginalDomain S U _

namespace SourceCategory

/-- The independently constructed image-only quotient comparison is exactly
the image of the full strong comparison between the same actual domains. -/
theorem domainNestedMap_eq_strongFunctor
    (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    domainNestedMap S U = strongFunctor.map (nestedDomainStrongMap S U) := by
  apply (cancel_mono (domainInclusion (A.originalDomain S) U)).1
  erw [domainNestedMap_inclusion, ← Functor.map_comp,
    nestedDomainStrongMap_inclusion, ← domainMap_eq_strongFunctor]

/-- The full strong transport agrees with the actual quotient-Hom localization
on every supplied full strong arrow out of the nested domain. -/
theorem domainNestedMap_comp_strong
    (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (f : (A.originalDomain S).originalDomain U ⟶ B) :
    domainNestedMap S U ≫ strongFunctor.map f =
      strongFunctor.map
        (StrongHom.fromNestedOriginalDomain (A := A.presentation) (B := B.presentation)
          S U f) := by
  erw [domainNestedMap_eq_strongFunctor, ← Functor.map_comp, nestedDomainStrongMap_comp]
  rfl

end SourceCategory
end Langlands.Analytic.SaturatedAtlasPresentation
