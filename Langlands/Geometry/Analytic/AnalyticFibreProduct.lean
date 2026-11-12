import Langlands.Geometry.Analytic.FibreProductProjections
import Langlands.Geometry.Analytic.SaturatedComparisonEquivalence
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # Fibre products of saturated presentations and of analytic spaces -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y S : SaturatedAtlasPresentation.{u, u, u} K}

/-- The compatible strong map between original presentations that corresponds to a
strong map of saturated presentations under the comparison isomorphisms. -/
def compatibleMap (f : X ⟶ S) : CompatibleStrongHom X.presentation S.presentation :=
  StrongHom.originalRestriction (X.saturationIso.hom ≫ f ≫ S.saturationIso.inv)

theorem saturationExtension_compatibleMap (f : X ⟶ S) :
    (compatibleMap f).saturationExtension = X.saturationIso.hom ≫ f ≫ S.saturationIso.inv :=
  StrongHom.saturationExtension_originalRestriction _

/-- The saturation of `compatibleMap f`, as a morphism of saturated presentations. -/
abbrev saturatedMap (f : X ⟶ S) : ofSaturation X.presentation ⟶ ofSaturation S.presentation :=
  (compatibleMap f).saturationExtension

theorem saturatedMap_comp_saturationIso (f : X ⟶ S) :
    saturatedMap f ≫ S.saturationIso.hom = X.saturationIso.hom ≫ f := by
  unfold saturatedMap
  rw [saturationExtension_compatibleMap]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
theorem compatibleMap_baseMap (f : X ⟶ S) : (compatibleMap f).baseMap = f.baseMap := rfl

variable [T2Space X.presentation.space] [T2Space Y.presentation.space]
  [T2Space S.presentation.space] (f : X ⟶ S) (g : Y ⟶ S)

/-- The fibre product `X ×_S Y` of saturated presentations: the saturation of the glued
fibre product presentation. -/
def fibreProduct : SaturatedAtlasPresentation.{u, u, u} K :=
  ofSaturation (FibreProduct.presentation (compatibleMap f) (compatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains)

/-- The saturation of the first projection. -/
abbrev fstSaturated : fibreProduct f g ⟶ ofSaturation X.presentation :=
  (FibreProduct.fstHom (compatibleMap f) (compatibleMap g) X.hasAllLocalDomains
    Y.hasAllLocalDomains).saturationExtension

/-- The saturation of the second projection. -/
abbrev sndSaturated : fibreProduct f g ⟶ ofSaturation Y.presentation :=
  (FibreProduct.sndHom (compatibleMap f) (compatibleMap g) X.hasAllLocalDomains
    Y.hasAllLocalDomains).saturationExtension

/-- The first projection `X ×_S Y → X`. -/
def fibreProductFst : fibreProduct f g ⟶ X := fstSaturated f g ≫ X.saturationIso.hom

/-- The second projection `X ×_S Y → Y`. -/
def fibreProductSnd : fibreProduct f g ⟶ Y := sndSaturated f g ≫ Y.saturationIso.hom

theorem fibreProductFst_baseMap :
    (fibreProductFst f g).baseMap = ⟨FibreProduct.fst (compatibleMap f) (compatibleMap g),
      FibreProduct.continuous_fst _ _⟩ := rfl

theorem fibreProductSnd_baseMap :
    (fibreProductSnd f g).baseMap = ⟨FibreProduct.snd (compatibleMap f) (compatibleMap g),
      FibreProduct.continuous_snd _ _⟩ := rfl

/-- The fibre product square commutes. -/
theorem fibreProduct_condition :
    fibreProductFst f g ≫ f = fibreProductSnd f g ≫ g := by
  have e : fstSaturated f g ≫ saturatedMap f = sndSaturated f g ≫ saturatedMap g := by
    have h := congrArg CompatibleStrongHom.saturationExtension
      (FibreProduct.fstHom_comp (compatibleMap f) (compatibleMap g) X.hasAllLocalDomains
        Y.hasAllLocalDomains)
    rw [CompatibleStrongHom.saturationExtension_comp,
      CompatibleStrongHom.saturationExtension_comp] at h
    exact h
  calc fibreProductFst f g ≫ f = fstSaturated f g ≫ (X.saturationIso.hom ≫ f) :=
        Category.assoc _ _ _
    _ = fstSaturated f g ≫ (saturatedMap f ≫ S.saturationIso.hom) := by
        rw [saturatedMap_comp_saturationIso]
    _ = (fstSaturated f g ≫ saturatedMap f) ≫ S.saturationIso.hom := (Category.assoc _ _ _).symm
    _ = (sndSaturated f g ≫ saturatedMap g) ≫ S.saturationIso.hom := by rw [e]
    _ = sndSaturated f g ≫ (saturatedMap g ≫ S.saturationIso.hom) := Category.assoc _ _ _
    _ = sndSaturated f g ≫ (Y.saturationIso.hom ≫ g) := by
        rw [saturatedMap_comp_saturationIso]
    _ = fibreProductSnd f g ≫ g := (Category.assoc _ _ _).symm

/-- The fibre product square in the localized category of analytic spaces. -/
theorem localizationFunctor_fibreProduct_condition :
    localizationFunctor.map (fibreProductFst f g) ≫ localizationFunctor.map f =
      localizationFunctor.map (fibreProductSnd f g) ≫ localizationFunctor.map g := by
  rw [← Functor.map_comp, ← Functor.map_comp, fibreProduct_condition]

end Langlands.Analytic.SaturatedAtlasPresentation
