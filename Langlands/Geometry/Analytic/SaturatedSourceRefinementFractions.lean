import Langlands.Geometry.Analytic.SaturatedRightFractionComposition

/-! # Source-subatlas normal forms for saturated localized morphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- A downward-closed locally refining selection retains full local-domain
closure on the literal original ambient space. -/
def refiningSubpresentation (A : SaturatedAtlasPresentation.{u, v, w} K)
    (P : A.presentation.atlas.RefiningSelection) :
    SaturatedAtlasPresentation.{u, v, w} K where
  presentation := A.presentation.refiningSubpresentation P
  hasAllLocalDomains := A.presentation.atlas.subatlas_hasAllLocalDomains
    A.hasAllLocalDomains P.carrier P.locally_refining P.downward_closed

@[simp]
theorem refiningSubpresentation_space (P : A.presentation.atlas.RefiningSelection) :
    (A.refiningSubpresentation P).presentation.space = A.presentation.space := rfl

/-- Every admissible bounded pullback is an original atlas restriction. -/
def refiningSubatlasInclusion (A : SaturatedAtlasPresentation.{u, v, w} K)
    (P : A.presentation.atlas.RefiningSelection) : A.refiningSubpresentation P ⟶ A :=
  A.presentation.strongSubatlasInclusion P.carrier P.locally_refining

@[simp]
theorem refiningSubatlasInclusion_baseMap (P : A.presentation.atlas.RefiningSelection) :
    (A.refiningSubatlasInclusion P).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem refiningSubatlasInclusion_pullback (P : A.presentation.atlas.RefiningSelection)
    (i : (A.refiningSubpresentation P).presentation.atlas.Index)
    (j : A.presentation.atlas.Index)
    (h : (A.refiningSubatlasInclusion P).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart j)) :
    (A.refiningSubatlasInclusion P).pullback i j h =
      A.presentation.atlas.restriction i.val j (fun x hx => h ⟨x, hx, rfl⟩) := rfl

theorem isQuasiIso_refiningSubatlasInclusion (P : A.presentation.atlas.RefiningSelection) :
    (A.refiningSubatlasInclusion P).IsQuasiIso :=
  A.presentation.isQuasiIso_strongSubatlasInclusion P.carrier P.locally_refining

/-- Retain precisely the original source-object charts contained in an
original chart image of the fraction denominator. -/
def fractionSourceSelection
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    A.presentation.atlas.RefiningSelection where
  carrier := φ.hs.reverseChartSelection
  downward_closed := φ.hs.reverseChartSelection_downward
  locally_refining := φ.hs.reverseChartSelection_locallyRefining A.hasAllLocalDomains

@[simp]
theorem mem_fractionSourceSelection
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (j : A.presentation.atlas.Index) :
    j ∈ fractionSourceSelection φ ↔
      ∃ i, Set.range (A.presentation.atlas.chart j) ⊆
        φ.s.baseMap '' Set.range (φ.X'.presentation.atlas.chart i) := Iff.rfl

/-- The actual reverse bounded map from the selected original source charts
to the old fraction source, constructed from full affinoid-test uniqueness. -/
def fractionSourceReverse
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    A.refiningSubpresentation (fractionSourceSelection φ) ⟶ φ.X' :=
  (φ.hs.reverseCompatibleStrongMap (compatibleFunctor.map φ.s).coherent
    A.hasAllLocalDomains).toStrongHom

@[simp]
theorem fractionSourceReverse_baseMap
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    (fractionSourceReverse φ).baseMap = φ.hs.inverseBaseMap := rfl

/-- The reverse identity holds for complete strong maps, including every
admissible bounded algebra pullback. -/
theorem fractionSourceReverse_comp
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    fractionSourceReverse φ ≫ φ.s =
      A.refiningSubatlasInclusion (fractionSourceSelection φ) := by
  exact congrArg AffinoidAtlasPresentation.CompatibleStrongHom.toStrongHom
    ((compatibleFunctor.map φ.s).reverse_comp φ.hs A.hasAllLocalDomains)

/-- An actual strong numerator with canonical same-space subatlas denominator. -/
def sourceRefinementFraction (P : A.presentation.atlas.RefiningSelection)
    (g : A.refiningSubpresentation P ⟶ B) :
    (quasiIsomorphisms (K := K)).RightFraction A B :=
  ⟨A.refiningSubatlasInclusion P, isQuasiIso_refiningSubatlasInclusion P, g⟩

@[simp]
theorem sourceRefinementFraction_s_baseMap (P : A.presentation.atlas.RefiningSelection)
    (g : A.refiningSubpresentation P ⟶ B) :
    (sourceRefinementFraction P g).s.baseMap =
      ContinuousMap.id A.presentation.space := rfl

/-- Replace an arbitrary denominator by the actual reverse-chart subatlas
inclusion and compose the constructed reverse map with the old numerator. -/
def sourceRefinedFraction
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    (quasiIsomorphisms (K := K)).RightFraction A B :=
  sourceRefinementFraction (fractionSourceSelection φ) (fractionSourceReverse φ ≫ φ.f)

@[simp]
theorem sourceRefinedFraction_f_baseMap
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    (sourceRefinedFraction φ).f.baseMap =
      φ.f.baseMap.comp φ.hs.inverseBaseMap := rfl

/-- The explicit comparison maps are the identity of the new source and the
constructed reverse map to the old source. -/
theorem sourceRefinedFraction_commonRefinement
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    FractionCommonRefinement (sourceRefinedFraction φ) φ := by
  refine ⟨A.refiningSubpresentation (fractionSourceSelection φ),
    𝟙 _, fractionSourceReverse φ, ?_, ?_, ?_⟩
  · exact (Category.id_comp (obj := SaturatedAtlasPresentation.{u, v, w} K)
      (A.refiningSubatlasInclusion (fractionSourceSelection φ))).trans
        (fractionSourceReverse_comp φ).symm
  · exact Category.id_comp _
  · exact (Category.id_comp (obj := SaturatedAtlasPresentation.{u, v, w} K)
      (A.refiningSubatlasInclusion (fractionSourceSelection φ))).symm ▸
        isQuasiIso_refiningSubatlasInclusion (fractionSourceSelection φ)

/-- Normalization preserves the localized arrow by the full common refinement. -/
@[simp]
theorem localizedRightFraction_sourceRefinedFraction
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    localizedRightFraction (sourceRefinedFraction φ) = localizedRightFraction φ :=
  (localizedRightFraction_eq_iff _ _).2 (sourceRefinedFraction_commonRefinement φ)

/-- A canonical same-space inclusion has identity continuous map, so the
underlying map of its fraction is exactly the actual numerator map. -/
theorem localizedSpaceFunctor_map_sourceRefinementFraction
    (P : A.presentation.atlas.RefiningSelection) (g : A.refiningSubpresentation P ⟶ B) :
    localizedSpaceFunctor.map (localizedRightFraction (sourceRefinementFraction P g)) =
      TopCat.ofHom g.baseMap := by
  have h := congrArg localizedSpaceFunctor.map
    (localizationFunctor_map_s_comp_localizedRightFraction (sourceRefinementFraction P g))
  rw [Functor.map_comp, localizedSpaceFunctor_map, localizedSpaceFunctor_map] at h
  change 𝟙 A.presentation.space ≫
    localizedSpaceFunctor.map (localizedRightFraction (sourceRefinementFraction P g)) =
      TopCat.ofHom g.baseMap at h
  exact (Category.id_comp (obj := TopCat.{v}) _).symm.trans h

/-- Every localized arrow is an actual strong numerator on a downward-closed
locally refining subatlas of its original source's literal ambient space. -/
theorem exists_sourceRefinementFraction
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    ∃ (P : A.presentation.atlas.RefiningSelection) (g : A.refiningSubpresentation P ⟶ B),
      f = localizedRightFraction (sourceRefinementFraction P g) ∧
        localizedSpaceFunctor.map f = TopCat.ofHom g.baseMap := by
  obtain ⟨φ, hφ⟩ := exists_localizedRightFraction f
  refine ⟨fractionSourceSelection φ, fractionSourceReverse φ ≫ φ.f, ?_, ?_⟩
  · exact hφ.trans (localizedRightFraction_sourceRefinedFraction φ).symm
  · rw [hφ, ← localizedRightFraction_sourceRefinedFraction φ]
    exact localizedSpaceFunctor_map_sourceRefinementFraction _ _

end Langlands.Analytic.SaturatedAtlasPresentation
