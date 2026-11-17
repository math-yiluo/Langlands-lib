import Langlands.Geometry.Analytic.FibreProductSmallProjections
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # The actual same-universe saturated fibre-product square -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FibreProduct

variable {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [Small.{v} (chartSystem f g).Space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- The complete original strong projections commute as entire bounded maps. -/
theorem smallFstHom_comp :
    (smallFstHom f g hA hB hC).comp f = (smallSndHom f g hA hB hC).comp g := by
  have hb : ((smallFstHom f g hA hB hC).comp f).baseMap =
      ((smallSndHom f g hA hB hC).comp g).baseMap :=
    ContinuousMap.ext fun z => baseMap_fst f g ((smallSpaceHomeomorph f g hA hB hC).symm z)
  refine CompatibleStrongHom.ext_of_pullback hb fun T => ?_
  let p := smallRep f g hA hB hC T
  have h₁ : (smallFstHom f g hA hB hC).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart T) ⊆ range (A.atlas.chart p.val.1) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (smallFstBase_chart f g hA hB hC T x).symm ▸ ⟨_, rfl⟩
  have h₂ : (smallSndHom f g hA hB hC).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart T) ⊆ range (B.atlas.chart p.val.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (smallSndBase_chart f g hA hB hC T x).symm ▸ ⟨_, rfl⟩
  have hk : ((smallFstHom f g hA hB hC).comp f).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart T) ⊆
        range (C.atlas.chart (base f g p)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (isCommonBase_base f g p).1 ⟨_, h₁ ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨base f g p, hk, ?_⟩
  have el := CompatibleStrongHom.comp_pullback (smallFstHom f g hA hB hC) f T p.val.1
    (base f g p) h₁ (isCommonBase_base f g p).1 hk
  have er := CompatibleStrongHom.comp_pullback (smallSndHom f g hA hB hC) g T p.val.2
    (base f g p) h₂ (isCommonBase_base f g p).2 (by rw [← hb]; exact hk)
  refine el.trans (Eq.trans ?_ er.symm)
  change (smallFstPullback f g hA hB hC T p.val.1 h₁).comp (leftBase f g p) =
    (smallSndPullback f g hA hB hC T p.val.2 h₂).comp (rightBase f g p)
  unfold smallFstPullback smallSndPullback
  rw [A.atlas.changeMapChart_self, B.atlas.changeMapChart_self]
  exact AffinoidPushout.condition (leftBase f g p) (rightBase f g p)

end FibreProduct

namespace SaturatedAtlasPresentation

variable {X Y S : SaturatedAtlasPresentation.{u, v, v} K}

/-- The complete original compatible map of a saturated morphism. -/
abbrev geometricCompatibleMap (f : X ⟶ S) : CompatibleStrongHom X.presentation S.presentation :=
  CompatibleStrongHom.ofSaturated f X.hasAllLocalDomains

variable (f : X ⟶ S) (g : Y ⟶ S)
  [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space]

/-- The actual same-universe saturated object, conditional on quotient smallness. -/
def smallFibreProduct : SaturatedAtlasPresentation.{u, v, v} K :=
  ofSaturation (FibreProduct.smallPresentation (geometricCompatibleMap f) (geometricCompatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)

/-- The complete first projection into the original saturated object. -/
def smallFibreProductFst : smallFibreProduct f g ⟶ X :=
  (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains).saturationExtension ≫
      X.saturationIso.hom

/-- The complete second projection into the original saturated object. -/
def smallFibreProductSnd : smallFibreProduct f g ⟶ Y :=
  (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains).saturationExtension ≫
      Y.saturationIso.hom

/-- The small saturated square commutes as entire strong morphisms. -/
theorem smallFibreProduct_condition :
    smallFibreProductFst f g ≫ f = smallFibreProductSnd f g ≫ g := by
  let p : smallFibreProduct f g ⟶ ofSaturation X.presentation :=
    (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains).saturationExtension
  let q : smallFibreProduct f g ⟶ ofSaturation Y.presentation :=
    (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains).saturationExtension
  let F : ofSaturation X.presentation ⟶ ofSaturation S.presentation :=
    (geometricCompatibleMap f).saturationExtension
  let G : ofSaturation Y.presentation ⟶ ofSaturation S.presentation :=
    (geometricCompatibleMap g).saturationExtension
  have he : p ≫ F = q ≫ G := by
    have h := congrArg CompatibleStrongHom.saturationExtension
      (FibreProduct.smallFstHom_comp (geometricCompatibleMap f) (geometricCompatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)
    rw [CompatibleStrongHom.saturationExtension_comp,
      CompatibleStrongHom.saturationExtension_comp] at h
    exact h
  have hf : F ≫ S.saturationIso.hom =
      X.saturationIso.hom ≫ f := (saturationComparisonNatIso (K := K)).hom.naturality f
  have hg : G ≫ S.saturationIso.hom =
      Y.saturationIso.hom ≫ g := (saturationComparisonNatIso (K := K)).hom.naturality g
  change (p ≫ X.saturationIso.hom) ≫ f = (q ≫ Y.saturationIso.hom) ≫ g
  calc
    (p ≫ X.saturationIso.hom) ≫ f = p ≫ (F ≫ S.saturationIso.hom) := by rw [Category.assoc, hf]
    _ = (p ≫ F) ≫ S.saturationIso.hom :=
      (Category.assoc _ _ _).symm
    _ = (q ≫ G) ≫ S.saturationIso.hom := by rw [he]
    _ = (q ≫ Y.saturationIso.hom) ≫ g := by rw [Category.assoc, hg, ← Category.assoc]

end SaturatedAtlasPresentation

end Langlands.Analytic
