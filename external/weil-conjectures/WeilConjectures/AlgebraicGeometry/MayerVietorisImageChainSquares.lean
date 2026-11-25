/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.OpenImageDirectImageComparisonRestriction

/-! # Explicit restriction-induced comparison maps

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-image-chain-data).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

attribute [local irreducible] schemeMVImageIso schemeOpenModuleImageRestriction
  schemeMVUnderivedOpenRestriction schemeMVUnderivedOpenComposition
  schemeOpenModuleAdjunction schemeOpenRestrictionCompIso

private theorem pushforwardCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g) :
    Scheme.Modules.pushforwardCongr hf = eqToIso (congrArg Scheme.Modules.pushforward hf) := by
  subst g
  ext M T a
  simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Scheme.Modules.Hom.id_app]
  simp

private theorem schemeMVImageIso_eq {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens) :
    schemeMVImageIso h W = schemeOpenImageDirectImageComparison h W := by
  unfold schemeMVImageIso schemeOpenImageDirectImageComparison schemeMVUnderivedOpenComposition
  rw [pushforwardCongr_eq]
  rfl

private theorem schemeMVImageIso_unit {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
        ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ W)).unit.app M) ≫
      (schemeMVImageIso h W).hom.app M =
    (schemeOpenModuleAdjunction Y W).unit.app
      ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).obj M) := by
  rw [schemeMVImageIso_eq]
  exact schemeOpenImageDirectImageComparison_unit X Y h W M

private theorem schemeMVImageIso_restriction {X Y : Scheme.{u}} (h : X ⟶ Y)
    {W A : Y.Opens} (i : W ⟶ A)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
        ((schemeOpenModuleImageRestriction X ((Opens.map h.base).map i)).app M) ≫
      (schemeMVImageIso h W).hom.app M =
    (schemeMVImageIso h A).hom.app M ≫
      (schemeOpenModuleImageRestriction Y i).app
        ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).obj M) := by
  rw [schemeMVImageIso_eq, schemeMVImageIso_eq]
  exact (schemeOpenImageDirectImageComparison_restriction X Y h i M).symm

private theorem image_unit_complex {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ W) I) ≫
        schemeMVImageComponent h W I J f =
      f ≫ schemeOpenModuleImageComplexUnit Y W J := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
      ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ W)).unit.app (I.X n)) ≫
    ((schemeMVImageIso h W).hom.app (I.X n) ≫
      (schemeOpenModuleImage Y W).map (f.f n)) =
    f.f n ≫ (schemeOpenModuleAdjunction Y W).unit.app (J.X n)
  rw [← Category.assoc, schemeMVImageIso_unit]
  exact ((schemeOpenModuleAdjunction Y W).unit.naturality (f.f n)).symm

private theorem image_restriction_complex {X Y : Scheme.{u}} (h : X ⟶ Y)
    {W A : Y.Opens} (i : W ⟶ A)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).map (schemeOpenModuleImageComplexRestriction X
        ((Opens.map h.base).map i) I) ≫ schemeMVImageComponent h W I J f =
      schemeMVImageComponent h A I J f ≫ schemeOpenModuleImageComplexRestriction Y i J := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
      ((schemeOpenModuleImageRestriction X ((Opens.map h.base).map i)).app (I.X n)) ≫
    ((schemeMVImageIso h W).hom.app (I.X n) ≫
      (schemeOpenModuleImage Y W).map (f.f n)) =
    ((schemeMVImageIso h A).hom.app (I.X n) ≫
      (schemeOpenModuleImage Y A).map (f.f n)) ≫
        (schemeOpenModuleImageRestriction Y i).app (J.X n)
  rw [← Category.assoc, schemeMVImageIso_restriction]
  simp only [Category.assoc]
  have hn :
      (schemeOpenModuleImage Y A).map (f.f n) ≫
          (schemeOpenModuleImageRestriction Y i).app (J.X n) =
        (schemeOpenModuleImageRestriction Y i).app
            ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).obj (I.X n)) ≫
          (schemeOpenModuleImage Y W).map (f.f n) :=
    (schemeOpenModuleImageRestriction Y i).naturality (f.f n)
  exact congrArg (fun k ↦ (schemeMVImageIso h A).hom.app (I.X n) ≫ k) hn.symm

-- Use the proved degreewise API without unfolding the sectionwise map constructions.
attribute [local irreducible] schemeMVImageComponent
  schemeOpenModuleImageComplexRestriction

-- Keep the additive calculation abstract: its inputs are the proved map equations.
private theorem map_biprod_desc_square
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {A B T : C} {A' B' T' : D}
    (r : A ⟶ T) (s : B ⟶ T) (r' : A' ⟶ T') (s' : B' ⟶ T')
    (a : F.obj A ⟶ A') (b : F.obj B ⟶ B') (t : F.obj T ⟶ T')
    (hr : F.map r ≫ t = a ≫ r') (hs : F.map s ≫ t = b ≫ s') :
    F.map (biprod.desc r (-s)) ≫ t =
      biprod.lift (F.map biprod.fst ≫ a) (F.map biprod.snd ≫ b) ≫
        biprod.desc r' (-s') := by
  rw [biprod.desc_eq, F.map_add, F.map_comp, F.map_comp, F.map_neg]
  simp only [Preadditive.add_comp, Preadditive.comp_neg, Preadditive.neg_comp,
    Category.assoc, biprod.lift_desc]
  rw [hr, hs]

/-- The explicit image components commute with the pair of units and the
restriction difference. Source: Stacks Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-image-chain-squares).

Proof: On a test open A, the comparison is the identity identifying
I(h⁻¹(A ∩ W)) with I(h⁻¹(A) ∩ h⁻¹(W)); scalar actions agree by the
restriction formula for h-sharp. It commutes with restrictions to smaller
opens. Thus h_* of each restriction unit, followed by the comparison and
restriction of f, is f followed by the corresponding restriction unit of J.
The two components give the first square by the biproduct universal property.
The same naturality for U ∩ V ⊆ U and U ∩ V ⊆ V gives the second square;
additivity preserves its minus sign. The sectionwise calculation uses only
functorial restriction, so also applies to empty and repeated opens. -/
theorem schemeMV_image_chain_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let b := biprod.lift
      (F.map biprod.fst ≫ schemeMVImageComponent h U I J f)
      (F.map biprod.snd ≫ schemeMVImageComponent h V I J f)
    (F.map (schemeMayerVietorisF X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I) ≫ b =
      f ≫ schemeMayerVietorisF Y U V J) ∧
    (F.map (schemeMayerVietorisG X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I) ≫
        schemeMVImageComponent h (U ⊓ V) I J f =
      b ≫ schemeMayerVietorisG Y U V J) := by
  dsimp only
  constructor
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, schemeMayerVietorisF]
      rw [← Category.assoc, ← Functor.map_comp, biprod.lift_fst]
      exact image_unit_complex h U I J f
    · simp only [Category.assoc, biprod.lift_snd, schemeMayerVietorisF]
      rw [← Category.assoc, ← Functor.map_comp, biprod.lift_snd]
      exact image_unit_complex h V I J f
  · set_option backward.isDefEq.respectTransparency false in
    exact map_biprod_desc_square
      ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
      (schemeOpenModuleImageComplexRestriction X
        ((Opens.map h.base).map (homOfLE (show U ⊓ V ≤ U from inf_le_left))) I)
      (schemeOpenModuleImageComplexRestriction X
        ((Opens.map h.base).map (homOfLE (show U ⊓ V ≤ V from inf_le_right))) I)
      (schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_left) J)
      (schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_right) J)
      (schemeMVImageComponent h U I J f) (schemeMVImageComponent h V I J f)
      (schemeMVImageComponent h (U ⊓ V) I J f)
      (image_restriction_complex h (homOfLE inf_le_left) I J f)
      (image_restriction_complex h (homOfLE inf_le_right) I J f)

end AlgebraicGeometry
