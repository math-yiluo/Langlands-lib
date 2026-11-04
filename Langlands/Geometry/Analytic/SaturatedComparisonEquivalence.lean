import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction
import Mathlib.CategoryTheory.Equivalence

/-! # Actual comparison with enlargement and equivalence of atlas categories -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, v} K)

/-- The actual original-to-enlarged comparison when both index types lie in
the ambient universe. Its pullbacks are the existing local-domain arrows. -/
def directToSaturation : StrongHom A A.saturatedPresentation where
  baseMap := ContinuousMap.id A.space
  target_exists i := by
    refine ⟨A.atlas.originalSaturatedIndex i, ?_⟩
    change id '' Set.range (A.atlas.chart i) ⊆
      Set.range (A.atlas.saturatedChart (A.atlas.originalSaturatedIndex i))
    rw [Set.image_id, A.atlas.range_saturatedChart]
    exact Subset.rfl
  pullback i S h := (A.atlas.originalToSaturatedInclusion i S
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm i S h x :=
    ((A.atlas.originalToSaturatedInclusion i S _).ambientMap_naturality x).trans
      (A.atlas.originalLocalDomain_ambientMap i x)
  restriction_comm i i' S T hi hST h h' := by
    let p := A.atlas.originalToSaturatedInclusion i S
      (fun x hx => h ⟨x, hx, rfl⟩)
    let q := A.atlas.originalToSaturatedInclusion i' T
      (fun x hx => h' ⟨x, hx, rfl⟩)
    let f : A.atlas.originalLocalDomain i ⟶ A.atlas.originalLocalDomain i' :=
      LocalDomain.Inclusion.ofSubset _ _ (by
        rw [A.atlas.originalLocalDomain_locus, A.atlas.originalLocalDomain_locus]
        exact hi)
    let g := A.atlas.saturatedInclusion S T hST
    have heq := congrArg LocalDomain.Inclusion.restriction
      (@Subsingleton.elim (LocalDomain.Inclusion
        (A.atlas.originalLocalDomain i) (A.atlas.saturatedRepresentative T))
        inferInstance (f ≫ q) (p ≫ g))
    rw [LocalDomain.Inclusion.restriction_comp,
      A.atlas.originalLocalDomain_restriction i i' hi f] at heq
    exact heq

/-- The reverse actual comparison in the same index universe. Every
admissible pullback is the existing full local-domain bounded restriction. -/
def directFromSaturation : StrongHom A.saturatedPresentation A where
  baseMap := ContinuousMap.id A.space
  target_exists S := by
    refine ⟨(A.atlas.saturatedRepresentative S).index, ?_⟩
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(A.atlas.saturatedRepresentative S).domain.spectrumMap x, rfl⟩
  pullback S i h := (A.atlas.saturatedToOriginalInclusion S i
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm S i h x :=
    (A.atlas.originalLocalDomain_ambientMap i
      (BanachSpectrum.comap
        (A.atlas.saturatedToOriginalInclusion S i _).restriction.toBoundedRingHom x)).symm.trans
      ((A.atlas.saturatedToOriginalInclusion S i _).ambientMap_naturality x)
  restriction_comm S T i j hST hij h h' := by
    let p := A.atlas.saturatedToOriginalInclusion S i
      (fun x hx => h ⟨x, hx, rfl⟩)
    let q := A.atlas.saturatedToOriginalInclusion T j
      (fun x hx => h' ⟨x, hx, rfl⟩)
    let f := A.atlas.saturatedInclusion S T hST
    let g : A.atlas.originalLocalDomain i ⟶ A.atlas.originalLocalDomain j :=
      LocalDomain.Inclusion.ofSubset _ _ (by
        rw [A.atlas.originalLocalDomain_locus, A.atlas.originalLocalDomain_locus]
        exact hij)
    have heq := congrArg LocalDomain.Inclusion.restriction
      (@Subsingleton.elim (LocalDomain.Inclusion
        (A.atlas.saturatedRepresentative S) (A.atlas.originalLocalDomain j))
        inferInstance (f ≫ q) (p ≫ g))
    rw [LocalDomain.Inclusion.restriction_comp,
      LocalDomain.Inclusion.restriction_comp,
      A.atlas.originalLocalDomain_restriction i j hij g] at heq
    exact heq

@[simp]
theorem directToSaturation_baseMap :
    A.directToSaturation.baseMap = ContinuousMap.id A.space := rfl

@[simp]
theorem directFromSaturation_baseMap :
    A.directFromSaturation.baseMap = ContinuousMap.id A.space := rfl

/-- The comparison represents every relative chart image on all affinoid
tests, using the existing actual local-domain inclusion representation. -/
theorem isQuasiIso_directToSaturation : A.directToSaturation.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i S h
  have hlocus : A.directToSaturation.chartImageLocus i S =
      (A.atlas.saturatedRepresentative S).ambientMap ⁻¹'
        (A.atlas.originalLocalDomain i).locus := by
    change (A.atlas.saturatedChart S) ⁻¹' (id '' Set.range (A.atlas.chart i)) = _
    rw [Set.image_id, A.atlas.originalLocalDomain_locus]
    rfl
  rw [hlocus]
  exact (A.atlas.originalToSaturatedInclusion i S
    (fun x hx => h ⟨x, hx, rfl⟩)).represents

theorem isQuasiIso_directFromSaturation : A.directFromSaturation.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro S i h
  have hlocus : A.directFromSaturation.chartImageLocus S i =
      (A.atlas.originalLocalDomain i).ambientMap ⁻¹'
        (A.atlas.saturatedRepresentative S).locus := by
    ext x
    change A.atlas.chart i x ∈
        id '' Set.range (A.atlas.saturatedRepresentative S).ambientMap ↔
      (A.atlas.originalLocalDomain i).ambientMap x ∈
        (A.atlas.saturatedRepresentative S).locus
    erw [Set.image_id, (A.atlas.saturatedRepresentative S).range_ambientMap,
      A.atlas.originalLocalDomain_ambientMap]
  rw [hlocus]
  exact (A.atlas.saturatedToOriginalInclusion S i
    (fun x hx => h ⟨x, hx, rfl⟩)).represents

/-- Full bounded inverse law on the original saturated presentation. -/
theorem directToSaturation_comp_directFromSaturation
    (ha : A.atlas.HasAllLocalDomains) :
    A.directToSaturation.saturatedComp A.directFromSaturation
      ha A.atlas.saturatedAtlas_hasAllLocalDomains = StrongHom.id A := by
  refine StrongHom.ext_of_saturated ha rfl ?_
  intro i
  let I : A.saturatedPresentation.atlas.Index := A.atlas.originalSaturatedIndex i
  have hto : A.directToSaturation.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (A.saturatedPresentation.atlas.chart I) := by
    change id '' Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.saturatedChart I)
    rw [Set.image_id, A.atlas.range_saturatedChart]
    exact Subset.rfl
  have hfrom : A.directFromSaturation.baseMap ''
      Set.range (A.saturatedPresentation.atlas.chart I) ⊆ Set.range (A.atlas.chart i) := by
    change id '' Set.range (A.atlas.saturatedChart I) ⊆ Set.range (A.atlas.chart i)
    rw [Set.image_id, A.atlas.range_saturatedChart]
    exact Subset.rfl
  have hc := A.directToSaturation.comp_admissible A.directFromSaturation i I i hto hfrom
  refine ⟨i, hc, ?_⟩
  refine (A.directToSaturation.saturatedComp_pullback A.directFromSaturation ha
    A.atlas.saturatedAtlas_hasAllLocalDomains i I i hto hfrom hc).trans ?_
  let p := A.atlas.originalToSaturatedInclusion i I (fun x hx => hto ⟨x, hx, rfl⟩)
  let q := A.atlas.saturatedToOriginalInclusion I i (fun x hx => hfrom ⟨x, hx, rfl⟩)
  have he := congrArg LocalDomain.Inclusion.restriction
    (@Subsingleton.elim (LocalDomain.Inclusion
      (A.atlas.originalLocalDomain i) (A.atlas.originalLocalDomain i))
      inferInstance (p ≫ q) (𝟙 (A.atlas.originalLocalDomain i)))
  change p.restriction.comp q.restriction = _
  change p.restriction.comp q.restriction = BoundedAlgHom.id K (A.atlas.algebra i) at he
  change _ = A.atlas.restriction i i Subset.rfl
  rw [A.atlas.restriction_id]
  exact he

/-- Full bounded inverse law on the enlargement. Every new source has an
original parent, and local-domain arrow uniqueness determines its composite. -/
theorem directFromSaturation_comp_directToSaturation
    (ha : A.atlas.HasAllLocalDomains) :
    A.directFromSaturation.saturatedComp A.directToSaturation
      A.atlas.saturatedAtlas_hasAllLocalDomains ha =
        StrongHom.id A.saturatedPresentation := by
  refine StrongHom.ext_of_saturated A.atlas.saturatedAtlas_hasAllLocalDomains rfl ?_
  intro S
  let i := (A.atlas.saturatedRepresentative S).index
  let I : A.saturatedPresentation.atlas.Index := A.atlas.originalSaturatedIndex i
  have hfrom : A.directFromSaturation.baseMap ''
      Set.range (A.saturatedPresentation.atlas.chart S) ⊆ Set.range (A.atlas.chart i) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(A.atlas.saturatedRepresentative S).domain.spectrumMap x, rfl⟩
  have hto : A.directToSaturation.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (A.saturatedPresentation.atlas.chart I) := by
    change id '' Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.saturatedChart I)
    rw [Set.image_id, A.atlas.range_saturatedChart]
    exact Subset.rfl
  have hc := A.directFromSaturation.comp_admissible A.directToSaturation S i I hfrom hto
  refine ⟨I, hc, ?_⟩
  refine (A.directFromSaturation.saturatedComp_pullback A.directToSaturation
    A.atlas.saturatedAtlas_hasAllLocalDomains ha S i I hfrom hto hc).trans ?_
  have hSI : Set.range (A.atlas.saturatedChart S) ⊆
      Set.range (A.atlas.saturatedChart I) := fun x hx => hc ⟨x, hx, rfl⟩
  let p := A.atlas.saturatedToOriginalInclusion S i (fun x hx => hfrom ⟨x, hx, rfl⟩)
  let q := A.atlas.originalToSaturatedInclusion i I (fun x hx => hto ⟨x, hx, rfl⟩)
  have he := congrArg LocalDomain.Inclusion.restriction
    (@Subsingleton.elim (LocalDomain.Inclusion
      (A.atlas.saturatedRepresentative S) (A.atlas.saturatedRepresentative I))
      inferInstance (p ≫ q) (A.atlas.saturatedInclusion S I hSI))
  exact he

end AffinoidAtlasPresentation

namespace SaturatedAtlasPresentation

/-- A saturated presentation is actually isomorphic to its constructed
enlargement by the complete local-domain comparison families. -/
def saturationIso (S : SaturatedAtlasPresentation.{u, v, v} K) :
    ofSaturation S.presentation ≅ S where
  hom := S.presentation.directFromSaturation
  inv := S.presentation.directToSaturation
  hom_inv_id := S.presentation.directFromSaturation_comp_directToSaturation S.hasAllLocalDomains
  inv_hom_id := S.presentation.directToSaturation_comp_directFromSaturation S.hasAllLocalDomains

@[simp]
theorem saturationIso_hom_baseMap (S : SaturatedAtlasPresentation.{u, v, v} K) :
    S.saturationIso.hom.baseMap = ContinuousMap.id S.presentation.space := rfl

@[simp]
theorem saturationIso_inv_baseMap (S : SaturatedAtlasPresentation.{u, v, v} K) :
    S.saturationIso.inv.baseMap = ContinuousMap.id S.presentation.space := rfl

end SaturatedAtlasPresentation

namespace CompatibleAtlasPresentation

/-- Every object of the actual saturated category is isomorphic to the
constructed enlargement of its original presentation. The equal index
universes are part of this instance's type. -/
instance : (saturationFunctor (K := K) :
    CompatibleAtlasPresentation.{u, v, v} K ⥤ _).EssSurj where
  mem_essImage S := ⟨⟨S.presentation⟩, ⟨S.saturationIso⟩⟩

instance : (saturationFunctor (K := K) :
    CompatibleAtlasPresentation.{u, v, v} K ⥤ _).IsEquivalence where

/-- The original compatible category and the existing saturated category
are equivalent by the actual saturation functor. The inverse is Mathlib's
full-faithful essentially-surjective inverse, using the actual comparison
isomorphisms just constructed. -/
def saturationEquivalence : CompatibleAtlasPresentation.{u, v, v} K ≌
    SaturatedAtlasPresentation.{u, v, v} K :=
  (saturationFunctor (K := K)).asEquivalence

@[simp]
theorem saturationEquivalence_functor :
    (saturationEquivalence (K := K)).functor = saturationFunctor := rfl

/-- The equivalence's forward functor retains the literal ambient spaces
and continuous maps. -/
theorem saturationEquivalence_spaceFunctor :
    (saturationEquivalence (K := K)).functor ⋙ SaturatedAtlasPresentation.spaceFunctor =
      (spaceFunctor : CompatibleAtlasPresentation.{u, v, v} K ⥤ _) := rfl

end CompatibleAtlasPresentation
end Langlands.Analytic
