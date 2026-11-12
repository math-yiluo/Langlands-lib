import Langlands.CategoryTheory.RightFractionCoproducts
import Langlands.Geometry.Analytic.AtlasDisjointUnionStrongMaps
import Langlands.Geometry.Analytic.CompatibleStrongSubatlasRefinement
import Langlands.Geometry.Analytic.SaturatedComparisonEquivalence
import Langlands.Geometry.Analytic.SaturatedQuasiIsoRightFractions
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # Disjoint unions of analytic spaces in the localized category -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation

open AffinoidAtlasPresentation
open CompatibleAtlasPresentation (saturationFunctor quasiIsomorphisms_saturationFunctor_map_iff)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ## Replacement by presentations without empty charts -/

/-- The saturation of the presentation retaining exactly the nonempty original charts. -/
abbrev nonemptyReplacement (T : SaturatedAtlasPresentation.{u, v, v} K) :
    SaturatedAtlasPresentation.{u, v, v} K :=
  saturationFunctor.obj ⟨T.presentation.nonemptyPresentation⟩

/-- The compatible inclusion of the nonempty charts. -/
abbrev nonemptyCompatibleInclusion (T : SaturatedAtlasPresentation.{u, v, v} K) :
    (⟨T.presentation.nonemptyPresentation⟩ : CompatibleAtlasPresentation.{u, v, v} K) ⟶
      ⟨T.presentation⟩ :=
  T.presentation.compatibleSubatlasInclusion T.presentation.atlas.NonemptyChart
    T.presentation.atlas.nonemptyCharts_locallyRefining

/-- The comparison morphism from the replacement: the saturation of the inclusion of the
nonempty charts, followed by the comparison isomorphism of the saturated presentation. -/
def nonemptyReplacementHom (T : SaturatedAtlasPresentation.{u, v, v} K) :
    nonemptyReplacement T ⟶ T :=
  saturationFunctor.map (nonemptyCompatibleInclusion T) ≫ T.saturationIso.hom

@[simp]
theorem nonemptyReplacementHom_baseMap (T : SaturatedAtlasPresentation.{u, v, v} K) :
    (nonemptyReplacementHom T).baseMap = ContinuousMap.id T.presentation.space := rfl

theorem isQuasiIso_nonemptyReplacementHom (T : SaturatedAtlasPresentation.{u, v, v} K) :
    (nonemptyReplacementHom T).IsQuasiIso :=
  (quasiIsomorphisms (K := K)).comp_mem _ _
    ((quasiIsomorphisms_saturationFunctor_map_iff _).mpr
      (T.presentation.isQuasiIso_compatibleSubatlasInclusion _ _))
    T.presentation.isQuasiIso_directFromSaturation

/-- The comparison isomorphism of a saturated presentation, with its source written as the
image of the saturation functor. -/
def saturationFunctorIso (Y : SaturatedAtlasPresentation.{u, v, v} K) :
    saturationFunctor.obj ⟨Y.presentation⟩ ≅ Y :=
  Y.saturationIso

/-! ## Chosen disjoint unions of replacements -/

variable {J : Type z}

/-- The nonempty-chart presentations of a family. -/
abbrev nonemptyFamily (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) :
    J → AffinoidAtlasPresentation.{u, max z v, max z v} K :=
  fun j => (T j).presentation.nonemptyPresentation

theorem nonemptyFamily_hasNonemptyCharts
    (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) (j : J) :
    (nonemptyFamily T j).atlas.HasNonemptyCharts :=
  (T j).presentation.atlas.nonemptySubatlas_hasNonemptyCharts

/-- The disjoint union of the nonempty-chart presentations, as a compatible object. -/
abbrev sigmaCompatible (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) :
    CompatibleAtlasPresentation.{u, max z v, max z v} K :=
  ⟨AtlasDisjointUnion.presentation (nonemptyFamily T) (nonemptyFamily_hasNonemptyCharts T)⟩

/-- The compatible inclusion of a component. -/
abbrev compatibleInclusion (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    (j : J) :
    (⟨nonemptyFamily T j⟩ : CompatibleAtlasPresentation.{u, max z v, max z v} K) ⟶
      sigmaCompatible T :=
  AtlasDisjointUnion.compatibleInclusion (nonemptyFamily T) (nonemptyFamily_hasNonemptyCharts T) j

/-- The compatible morphism out of the disjoint union with given components. -/
abbrev compatibleDesc (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {B : CompatibleAtlasPresentation.{u, max z v, max z v} K}
    (g : ∀ j, (⟨nonemptyFamily T j⟩ : CompatibleAtlasPresentation.{u, max z v, max z v} K) ⟶ B) :
    sigmaCompatible T ⟶ B :=
  AtlasDisjointUnion.compatibleDesc (hA := nonemptyFamily_hasNonemptyCharts T) (B := B.presentation) g

theorem compatibleInclusion_desc (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {B : CompatibleAtlasPresentation.{u, max z v, max z v} K}
    (g : ∀ j, (⟨nonemptyFamily T j⟩ : CompatibleAtlasPresentation.{u, max z v, max z v} K) ⟶ B)
    (j : J) : compatibleInclusion T j ≫ compatibleDesc T g = g j :=
  AtlasDisjointUnion.inclusion_comp_desc g j

theorem compatible_hom_ext (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {B : CompatibleAtlasPresentation.{u, max z v, max z v} K} {g g' : sigmaCompatible T ⟶ B}
    (h : ∀ j, compatibleInclusion T j ≫ g = compatibleInclusion T j ≫ g') : g = g' :=
  AtlasDisjointUnion.compatibleHom_ext h

/-- The compatible componentwise morphism between disjoint unions. -/
abbrev compatibleSigmaMap (T X : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    (σ : ∀ j, (⟨nonemptyFamily T j⟩ : CompatibleAtlasPresentation.{u, max z v, max z v} K) ⟶
      ⟨nonemptyFamily X j⟩) :
    sigmaCompatible T ⟶ sigmaCompatible X :=
  AtlasDisjointUnion.map (nonemptyFamily_hasNonemptyCharts X)
    (nonemptyFamily_hasNonemptyCharts T) σ

theorem compatibleInclusion_map (T X : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    (σ : ∀ j, (⟨nonemptyFamily T j⟩ : CompatibleAtlasPresentation.{u, max z v, max z v} K) ⟶
      ⟨nonemptyFamily X j⟩) (j : J) :
    compatibleInclusion T j ≫ compatibleSigmaMap T X σ = σ j ≫ compatibleInclusion X j :=
  AtlasDisjointUnion.inclusion_comp_map (nonemptyFamily_hasNonemptyCharts T) σ j

/-- The saturation of the disjoint union of the nonempty-chart presentations. -/
abbrev sigmaPresentation (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) :
    SaturatedAtlasPresentation.{u, max z v, max z v} K :=
  saturationFunctor.obj (sigmaCompatible T)

theorem sigmaPresentation_space (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) :
    ((sigmaPresentation T).presentation.space : Type (max z v)) =
      ((j : J) × (T j).presentation.space) := rfl

/-- The chosen disjoint union of the replacements, with the saturated inclusions. -/
def sigmaCofan (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) :
    Cofan fun j => nonemptyReplacement (T j) :=
  Cofan.mk (sigmaPresentation T) fun j => saturationFunctor.map (compatibleInclusion T j)

theorem sigmaCofan_inj (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) (j : J) :
    (sigmaCofan T).inj j = saturationFunctor.map (compatibleInclusion T j) := rfl

/-- The descended morphism out of the chosen disjoint union. -/
def sigmaDesc (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {Y : SaturatedAtlasPresentation.{u, max z v, max z v} K}
    (f : ∀ j, nonemptyReplacement (T j) ⟶ Y) : sigmaPresentation T ⟶ Y :=
  saturationFunctor.map (compatibleDesc T fun j =>
      saturationFunctor.preimage (f j ≫ (saturationFunctorIso Y).inv)) ≫
    (saturationFunctorIso Y).hom

theorem inj_sigmaDesc (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {Y : SaturatedAtlasPresentation.{u, max z v, max z v} K}
    (f : ∀ j, nonemptyReplacement (T j) ⟶ Y) (j : J) :
    saturationFunctor.map (compatibleInclusion T j) ≫ sigmaDesc T f = f j := by
  rw [sigmaDesc, ← Category.assoc, ← Functor.map_comp, compatibleInclusion_desc,
    Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Morphisms out of the chosen disjoint union are determined on the components. -/
theorem sigma_hom_ext (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {Y : SaturatedAtlasPresentation.{u, max z v, max z v} K} (m m' : sigmaPresentation T ⟶ Y)
    (h : ∀ j, saturationFunctor.map (compatibleInclusion T j) ≫ m =
      saturationFunctor.map (compatibleInclusion T j) ≫ m') : m = m' := by
  have key : ∀ n : sigmaPresentation T ⟶ Y, n = saturationFunctor.map (saturationFunctor.preimage
      (n ≫ (saturationFunctorIso Y).inv)) ≫ (saturationFunctorIso Y).hom := fun n => by
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [key m, key m']
  congr 2
  refine compatible_hom_ext T fun j => saturationFunctor.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
    ← Category.assoc, ← Category.assoc, h j]

/-- The chosen disjoint union is a coproduct of the replacements. -/
def isColimitSigmaCofan (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) :
    IsColimit (sigmaCofan T) :=
  Cofan.IsColimit.mk _ (fun s => sigmaDesc T s.inj) (fun s j => inj_sigmaDesc T s.inj j)
    (fun s m hm => sigma_hom_ext T m (sigmaDesc T s.inj) fun j =>
      (hm j).trans (inj_sigmaDesc T s.inj j).symm)

/-- The morphism between chosen disjoint unions induced by quasi-isomorphisms is a
quasi-isomorphism. -/
theorem isQuasiIso_sigmaCofan_desc (T X : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    (s : ∀ j, nonemptyReplacement (T j) ⟶ nonemptyReplacement (X j))
    (hs : ∀ j, (s j).IsQuasiIso) :
    (Cofan.IsColimit.desc (isColimitSigmaCofan T)
      fun j => s j ≫ (sigmaCofan X).inj j).IsQuasiIso := by
  let σ : ∀ j, (⟨nonemptyFamily T j⟩ : CompatibleAtlasPresentation.{u, max z v, max z v} K) ⟶
      ⟨nonemptyFamily X j⟩ := fun j =>
    saturationFunctor.preimage (s j : saturationFunctor.obj ⟨nonemptyFamily T j⟩ ⟶
      saturationFunctor.obj ⟨nonemptyFamily X j⟩)
  have hσ : ∀ j, (σ j).toStrongHom.IsQuasiIso := fun j => by
    have e : saturationFunctor.map (σ j) = s j := Functor.map_preimage _ _
    apply (CompatibleAtlasPresentation.quasiIsomorphisms_saturationFunctor_map_iff (σ j)).mp
    rw [SaturatedAtlasPresentation.quasiIsomorphisms_iff, e]
    exact hs j
  have heq : (Cofan.IsColimit.desc (isColimitSigmaCofan T)
      fun j => s j ≫ (sigmaCofan X).inj j) = saturationFunctor.map (compatibleSigmaMap T X σ) := by
    refine Cofan.IsColimit.hom_ext (isColimitSigmaCofan T) _ _ fun j => ?_
    rw [Cofan.IsColimit.fac]
    show s j ≫ saturationFunctor.map (compatibleInclusion X j) =
      saturationFunctor.map (compatibleInclusion T j) ≫ saturationFunctor.map (compatibleSigmaMap T X σ)
    rw [← Functor.map_comp, compatibleInclusion_map, Functor.map_comp, Functor.map_preimage]
  rw [heq]
  exact (CompatibleAtlasPresentation.quasiIsomorphisms_saturationFunctor_map_iff _).mpr
    (AtlasDisjointUnion.isQuasiIso_map (nonemptyFamily_hasNonemptyCharts T) σ hσ)

variable (K J) in
/-- Chosen disjoint unions of saturated presentations, compatible with quasi-isomorphisms. -/
def rightFractionCoproducts :
    Langlands.CategoryTheory.RightFractionCoproducts
      (quasiIsomorphisms (K := K) :
        MorphismProperty (SaturatedAtlasPresentation.{u, max z v, max z v} K)) J where
  replace := nonemptyReplacement
  π := nonemptyReplacementHom
  π_mem := isQuasiIso_nonemptyReplacementHom
  sum := sigmaCofan
  isColimit := isColimitSigmaCofan
  desc_mem T X s hs := isQuasiIso_sigmaCofan_desc T X s hs

/-! ## Disjoint unions in the localized category -/

instance : (localizationFunctor (K := K) :
    SaturatedAtlasPresentation.{u, v, v} K ⥤ LocalizedCategory.{u, v, v} (K := K)).EssSurj :=
  Localization.essSurj _ (quasiIsomorphisms (K := K))

/-- The disjoint union of a family of analytic spaces. -/
def localizedSigma (X : J → LocalizedCategory.{u, max z v, max z v} (K := K)) :
    LocalizedCategory.{u, max z v, max z v} (K := K) :=
  localizationFunctor.obj (sigmaPresentation fun j => localizedObjectEquiv.symm (X j))

/-- The disjoint union of a family of analytic spaces with its inclusions. -/
def localizedSigmaCofan (X : J → LocalizedCategory.{u, max z v, max z v} (K := K)) : Cofan X :=
  (rightFractionCoproducts K J).originalCofan localizationFunctor
    fun j => localizedObjectEquiv.symm (X j)

theorem localizedSigmaCofan_pt (X : J → LocalizedCategory.{u, max z v, max z v} (K := K)) :
    (localizedSigmaCofan X).pt = localizedSigma X := rfl

/-- The disjoint union is a coproduct in the localized category. -/
def isColimitLocalizedSigmaCofan (X : J → LocalizedCategory.{u, max z v, max z v} (K := K)) :
    IsColimit (localizedSigmaCofan X) :=
  (rightFractionCoproducts K J).isColimitOriginalCofan (L := localizationFunctor)
    fun j => localizedObjectEquiv.symm (X j)

end Langlands.Analytic.SaturatedAtlasPresentation
