/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnit

/-! # A single derived unit across a commutative direct-image square

Source: Stacks Project, Cohomology, Tags 08FE and 0D5T.
(blueprint: lem-pc-direct-image-square-single-unit-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

set_option backward.isDefEq.respectTransparency.types false in
private theorem pushforwardCongr_eq {A D : Scheme.{u}}
    (v v' : A ⟶ D) (h : v = v') :
    (Scheme.Modules.pushforwardCongr h).hom =
      eqToHom (congrArg
        (fun f : A ⟶ D ↦ RingedSpace.moduleDirectImage f.toLRSHom.toShHom) h) := by
  subst v'
  ext M U
  simp
  rfl


set_option backward.isDefEq.respectTransparency.types false in
-- Preserve the equality expression used by the public statement. Expanding the
-- derived-functor family here makes the later source conversion expensive.
private theorem directImage_unit_congr {A D : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.toRingedSpace))]
    (v v' : A ⟶ D) (h : v = v')
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
        (eqToIso.{max (u + 1) w, max (u + 1) w} (congrArg schemeDerivedDirectImage h)).hom.app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (eqToHom (congrArg
            (fun f : A ⟶ D ↦ RingedSpace.moduleDirectImage f.toLRSHom.toShHom) h))
            (.up ℤ)).app K) ≫
        (RingedSpace.moduleDirectImage v'.toLRSHom.toShHom).rightDerivedFunctorUnit.app K := by
  subst v'
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
-- Keep the generic successive sources while transporting the single unit.
private theorem compositeUnit_congr {A B C D : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.toRingedSpace))]
    (s : A ⟶ B) (t : B ⟶ D) (q : A ⟶ C) (r : C ⟶ D) (e : s ≫ t = q ≫ r)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    schemeMVCompositionUnit s t K ≫
        (eqToIso.{max (u + 1) w, max (u + 1) w}
          (congrArg schemeDerivedDirectImage e)).hom.app
            (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (eqToHom (congrArg
            (fun f : A ⟶ D ↦ RingedSpace.moduleDirectImage f.toLRSHom.toShHom) e))
            (.up ℤ)).app K) ≫ schemeMVCompositionUnit q r K := by
  unfold schemeMVCompositionUnit
  exact directImage_unit_congr (s ≫ t) (q ≫ r) e K

private theorem model_eq (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace)) (.up ℤ)) :
    (schemeMVHomotopyOpenComposition h U).hom.app K =
      ((schemeMVUnderivedOpenComposition h U).hom.mapHomotopyCategory (.up ℤ)).app K := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient _ _).map _ ≫
    (HomotopyCategory.quotient _ _).map _ = (HomotopyCategory.quotient _ _).map _
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
-- Matching successive pushforwards with the composite unfolds scalar restrictions.
private theorem underived_eq (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens) :
    (schemeMVUnderivedOpenComposition h U).hom =
      eqToHom (congrArg
        (fun f : (h ⁻¹ᵁ U).toScheme ⟶ Y ↦
          RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
        (morphismRestrict_ι h U).symm) := by
  simp only [schemeMVUnderivedOpenComposition, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.pushforwardComp, SheafOfModules.pushforwardComp,
    Iso.refl_hom, Iso.refl_inv]
  rw [pushforwardCongr_eq]
  erw [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
-- Source identifications expand the successive direct-image functors.
/-- Equality transport of one derived unit, before factoring it into two units.
Source: Stacks Project, Cohomology, Tags 08FE and 0D5T.
Proof: the pushforward composition isomorphisms are identities on sections.
The intervening pushforwardCongr is equality transport along the commutative-square
identity. Pass to complexes degreewise and then to the homotopy quotient, obtaining
that the displayed homotopy comparison is the equality map of the homotopy direct
image objects. The right-derived unit is a family of natural transformations in
the scheme morphism. Equality induction on the square identity gives that its
component followed by equality transport of the derived functors equals equality
transport of its source followed by the other component. Functoriality of Qh on
equality maps identifies that source transport with the displayed Qh.map.
This uses arbitrary homotopy objects; zero complexes and empty schemes are included.
The displayed derived-category structures are independent; no global choice of
a derived category for every scheme is required.
(blueprint: lem-pc-direct-image-square-single-unit-normalization). -/
theorem schemeDirectImageSquare_single_unit_normalization
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
      (ComplexShape.up ℤ)) :
    schemeMVCompositionUnit (h ⁻¹ᵁ U).ι h K ≫
        (eqToIso.{max (u + 1) w, max (u + 1) w} (congrArg schemeDerivedDirectImage
          (morphismRestrict_ι h U).symm)).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((schemeMVHomotopyOpenComposition h U).hom.app K) ≫
        schemeMVCompositionUnit (h ∣_ U) U.ι K := by
  rw [model_eq, underived_eq]
  exact compositeUnit_congr (h ⁻¹ᵁ U).ι h (h ∣_ U) U.ι
    (morphismRestrict_ι h U).symm K

end AlgebraicGeometry
