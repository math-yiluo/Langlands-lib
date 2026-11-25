/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainSquares
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

/-- The restriction-induced morphism of Mayer--Vietoris complexes associated to a
normalized chain map.  Its three components are the chain map itself and the
sectionwise restriction-image maps on the two open terms and their intersection.
Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-image-chain-map) -/
def schemeMVImageChainMap {X Y : Scheme.{u}} (h : X ⟶ Y) (U V : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    (schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I).map
        ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)) ⟶
      schemeMayerVietorisComplex Y U V J := by
  let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let b := biprod.lift
      (F.map biprod.fst ≫ schemeMVImageComponent h U I J f)
      (F.map biprod.snd ≫ schemeMVImageComponent h V I J f)
  have hs := schemeMV_image_chain_squares X Y h U V I J f
  exact ShortComplex.homMk f b (schemeMVImageComponent h (U ⊓ V) I J f) hs.1.symm hs.2.symm

/-- A normalized chain representative for the direct-image morphism between the
fixed resolutions.  The target is K-injective, so fullness of the localization
produces this representative.
Source: Stacks Project, Tag 0D5T.
(blueprint: lem-pc-mayer-vietoris-normalized-chain-map) -/
theorem schemeMV_normalized_chain_map_exists
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X)
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))] :
    ∃ f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
        schemeMVResolution Y ((schemeDerivedDirectImage h).obj E),
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map f ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom := by
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let a := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I
  let b := schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)
  let φ := a.inv ≫
    (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom ≫ b.inv
  let e := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj _) J).surjective
      (e.hom.app _ ≫ φ ≫ e.inv.app J)
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective g
  have hq : DerivedCategory.Q.map f = φ := by
    have hn := e.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [hf, hg] at hn
    apply (cancel_epi (e.hom.app _)).mp
    simp only [Category.assoc] at hn
    erw [e.inv_hom_id_app J, Category.comp_id] at hn
    exact hn.symm
  refine ⟨f, ?_⟩
  change a.hom ≫ DerivedCategory.Q.map f ≫ b.hom = _
  rw [hq]
  simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

end AlgebraicGeometry
