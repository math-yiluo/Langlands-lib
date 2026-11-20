import Langlands.Geometry.Analytic.AnalyticOpenImmersionBaseChange
import Langlands.Geometry.Analytic.EtaleTargetDomain
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleRestriction
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Restriction of étale objects to an open subspace -/

noncomputable section

universe u v

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Limits TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The inverse image of `U` in `W`, as an étale object over the analytic space `U`. -/
def restrictEtaleObject (U : Opens (localizedSpaceFunctor.obj X)) (W : EtaleSite X) :
    EtaleSite (openEtaleObject X U).left :=
  MorphismProperty.Over.mk ⊤
    (preimageOpenDomainMap (Y := X) W.hom (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) (by
    apply etale_of_comp_domainι
    have h := preimageOpenDomainMap_comp (Y := X) W.hom
      (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
    exact (congrArg (fun f => etale f) h).mpr
      (etale_comp (etaleOpenDomainStatement W.left _ _) W.prop))

/-- The canonical inclusion of the restricted space into the original object. -/
def restrictEtaleInclusion (U : Opens (localizedSpaceFunctor.obj X)) (W : EtaleSite X) :
    (restrictEtaleObject X U W).left ⟶ W.left :=
  domainι W.left
    (preimageOpenDomain (Y := X) W.hom (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)

instance restrictEtaleInclusion_mono (U : Opens (localizedSpaceFunctor.obj X)) (W : EtaleSite X) :
    Mono (restrictEtaleInclusion X U W) :=
  domainι_mono _

/-- The two projections exhibit the restricted space as the pullback over `X`. -/
theorem isPullback_restrictEtale (U : Opens (localizedSpaceFunctor.obj X)) (W : EtaleSite X) :
    IsPullback (restrictEtaleObject X U W).hom (restrictEtaleInclusion X U W)
      (openEtaleObject X U).hom W.hom :=
  isPullback_preimageOpenDomain (Y := X) W.hom (U : Set (localizedSpaceFunctor.obj X)) U.isOpen

variable {X}

private def restrictEtaleMapLeft {U V : Opens (localizedSpaceFunctor.obj X)} (i : U ⟶ V)
    {W Z : EtaleSite X} (f : W ⟶ Z) :
    (restrictEtaleObject X U W).left ⟶ (restrictEtaleObject X V Z).left :=
  (isPullback_restrictEtale X V Z).lift
    ((restrictEtaleObject X U W).hom ≫ (openEtaleMap X i).left)
    (restrictEtaleInclusion X U W ≫ f.left) (by
      simp only [Category.assoc, MorphismProperty.Over.w (openEtaleMap X i),
        MorphismProperty.Over.w f]
      exact (isPullback_restrictEtale X U W).w)

@[reassoc (attr := simp)]
private theorem restrictEtaleMapLeft_fst {U V : Opens (localizedSpaceFunctor.obj X)} (i : U ⟶ V)
    {W Z : EtaleSite X} (f : W ⟶ Z) :
    restrictEtaleMapLeft i f ≫ (restrictEtaleObject X V Z).hom =
      (restrictEtaleObject X U W).hom ≫ (openEtaleMap X i).left :=
  (isPullback_restrictEtale X V Z).lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem restrictEtaleMapLeft_snd {U V : Opens (localizedSpaceFunctor.obj X)} (i : U ⟶ V)
    {W Z : EtaleSite X} (f : W ⟶ Z) :
    restrictEtaleMapLeft i f ≫ restrictEtaleInclusion X V Z =
      restrictEtaleInclusion X U W ≫ f.left :=
  (isPullback_restrictEtale X V Z).lift_snd _ _ _

variable (X)

private theorem openEtaleMap_id_left (U : Opens (localizedSpaceFunctor.obj X)) :
    (openEtaleMap X (𝟙 U)).left = 𝟙 (openEtaleObject X U).left :=
  congrArg (fun f : openEtaleObject X U ⟶ openEtaleObject X U => f.left)
    ((openEtaleFunctor X).map_id U)

/-- Restrict an étale object or morphism over `X` to the open analytic space `U`. -/
def restrictEtaleFunctor (U : Opens (localizedSpaceFunctor.obj X)) :
    EtaleSite X ⥤ EtaleSite (openEtaleObject X U).left where
  obj := restrictEtaleObject X U
  map f := MorphismProperty.Over.homMk (restrictEtaleMapLeft (𝟙 U) f) (by
    rw [restrictEtaleMapLeft_fst, openEtaleMap_id_left X]
    exact Category.comp_id _)
  map_id W := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (restrictEtaleInclusion X U W)).mp
    change restrictEtaleMapLeft (𝟙 U) (𝟙 W) ≫ restrictEtaleInclusion X U W = _
    simp
  map_comp {W Z T} f g := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (restrictEtaleInclusion X U T)).mp
    change restrictEtaleMapLeft (𝟙 U) (f ≫ g) ≫ restrictEtaleInclusion X U T =
      (restrictEtaleMapLeft (𝟙 U) f ≫ restrictEtaleMapLeft (𝟙 U) g) ≫
        restrictEtaleInclusion X U T
    simp [Category.assoc]

/-- Restriction as an endofunctor of the original étale site, varying covariantly in the open. -/
def etaleOpenRestrictionFunctor : Opens (localizedSpaceFunctor.obj X) ⥤ EtaleSite X ⥤ EtaleSite X where
  obj U := restrictEtaleFunctor X U ⋙ MorphismProperty.Over.map ⊤ (openEtaleObject X U).prop
  map {U V} i :=
    { app := fun W => MorphismProperty.Over.homMk (restrictEtaleMapLeft i (𝟙 W)) (by
        change restrictEtaleMapLeft i (𝟙 W) ≫
          ((restrictEtaleObject X V W).hom ≫ (openEtaleObject X V).hom) =
          (restrictEtaleObject X U W).hom ≫ (openEtaleObject X U).hom
        rw [← Category.assoc, restrictEtaleMapLeft_fst, Category.assoc,
          MorphismProperty.Over.w (openEtaleMap X i)])
      naturality := by
        intro W Z f
        apply MorphismProperty.Over.Hom.ext
        apply (cancel_mono (restrictEtaleInclusion X V Z)).mp
        change (restrictEtaleMapLeft (𝟙 U) f ≫ restrictEtaleMapLeft i (𝟙 Z)) ≫
            restrictEtaleInclusion X V Z =
          (restrictEtaleMapLeft i (𝟙 W) ≫ restrictEtaleMapLeft (𝟙 V) f) ≫
            restrictEtaleInclusion X V Z
        simp [Category.assoc] }
  map_id U := by
    ext W
    apply (cancel_mono (restrictEtaleInclusion X U W)).mp
    change restrictEtaleMapLeft (𝟙 U) (𝟙 W) ≫ restrictEtaleInclusion X U W =
      𝟙 (restrictEtaleObject X U W).left ≫ restrictEtaleInclusion X U W
    simp
  map_comp {U V T} i j := by
    ext W
    apply (cancel_mono (restrictEtaleInclusion X T W)).mp
    change restrictEtaleMapLeft (i ≫ j) (𝟙 W) ≫ restrictEtaleInclusion X T W =
      (restrictEtaleMapLeft i (𝟙 W) ≫ restrictEtaleMapLeft j (𝟙 W)) ≫
        restrictEtaleInclusion X T W
    simp [Category.assoc]

/-- The inclusion into the original object, natural in the étale object. -/
def etaleOpenRestrictionInclusion (U : Opens (localizedSpaceFunctor.obj X)) :
    (etaleOpenRestrictionFunctor X).obj U ⟶ 𝟭 (EtaleSite X) where
  app W := MorphismProperty.Over.homMk (restrictEtaleInclusion X U W)
    (isPullback_restrictEtale X U W).w.symm
  naturality := by
    intro W Z f
    apply MorphismProperty.Over.Hom.ext
    exact restrictEtaleMapLeft_snd (𝟙 U) f

@[reassoc (attr := simp)]
theorem etaleOpenRestrictionInclusion_naturality {U V : Opens (localizedSpaceFunctor.obj X)}
    (i : U ⟶ V) : (etaleOpenRestrictionFunctor X).map i ≫ etaleOpenRestrictionInclusion X V =
      etaleOpenRestrictionInclusion X U := by
  ext W
  change restrictEtaleMapLeft i (𝟙 W) ≫ restrictEtaleInclusion X V W =
    restrictEtaleInclusion X U W
  simp

end Langlands.Sheaf.Equivariant.Analytic
