/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The structure-sheaf unit comparison around a square

Source: Stacks Project, Tag 08HY; the ordinary pullback unit calculation.
(blueprint: lem-sc-pullback-structure-unit-square)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem structureUnit_comp
    {X Y Z : Scheme.{v}} (g : Z ⟶ Y) (f : Y ⟶ X) :
    (pullback g).map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom =
      (pullbackComp g f).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let U := SheafOfModules.unit X.ringCatSheaf
  let uf := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let ug := SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom
  let b := (pullback g).map uf ≫ ug
  let a := (pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction g)
  let a' := pullbackPushforwardAdjunction (g ≫ f)
  have hu := unit_conjugateEquiv a a' (pullbackComp g f).inv U
  rw [conjugateEquiv_pullbackComp_inv] at hu
  have hn := (pushforwardComp g f).hom.naturality b
  dsimp only [Functor.comp_map] at hn
  have ht : a'.homEquiv _ _ ((pullbackComp g f).inv.app U ≫ b) =
      a.homEquiv _ _ b ≫ (pushforwardComp g f).hom.app _ := by
    simp only [Adjunction.homEquiv_apply, Functor.map_comp, Category.assoc]
    rw [← Category.assoc, ← hu, Category.assoc]
    erw [← hn]
  have hb : a.homEquiv _ _ b =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (pushforward f).map (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
    change (pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackPushforwardAdjunction g).homEquiv _ _ ((pullback g).map uf ≫ ug)) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    dsimp only [uf, ug]
    erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hc : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (pushforward f).map (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
      (pushforwardComp g f).hom.app _ =
      SheafOfModules.unitToPushforwardObjUnit (g ≫ f).toRingCatSheafHom := by
    ext V
    rfl
  have he : (pullbackComp g f).inv.app U ≫ b =
      SheafOfModules.pullbackObjUnitToUnit (g ≫ f).toRingCatSheafHom := by
    apply (a'.homEquiv _ _).injective
    rw [ht, hb, Category.assoc, hc]
    exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _).symm
  have he' := congrArg (fun q ↦ (pullbackComp g f).hom.app U ≫ q) he
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, U, b, uf, ug] using he'

private theorem structureUnit_congr
    {X Y : Scheme.{v}} {f g : X ⟶ Y} (h : f = g) :
    (pullbackCongr h).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  subst g
  simp [pullbackCongr]

/-- Pullback of the structure-sheaf maps commutes with the ordinary square comparison.
There is no coefficient module, derived category or Picard test section here.
Source: Stacks Project, Tag 08HY; functoriality of pullback of the structure sheaf.
(blueprint: lem-sc-pullback-structure-unit-square)

Proof: Each pullbackObjUnitToUnit is the adjoint transpose of the ring-sheaf
 morphism sending 1 to 1. The inverse of pullbackComp is the conjugate of
 pushforward composition, so the composite adjunction identifies its unit
 comparison with successive pullback of these same ring-sheaf morphisms.
 Applying the Hom equivalence for the composite shows that pullbackComp
 followed by the composite unit comparison equals pullback of the first unit
 comparison followed by the second. Transport this identity along the square
 equality by equality elimination, and apply it to both paths. Cancel the
 common composite unit comparison to obtain the square. These are identities
 of ring and module maps and do not require a nonempty scheme or a nonzero ring. -/
theorem pullbackStructureUnitSquare
    {X S X' S' : Scheme.{v}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g) :
    let U := SheafOfModules.unit S.ringCatSheaf
    let c := (pullbackComp g' f).app U ≪≫ (pullbackCongr h).app U ≪≫
      ((pullbackComp f' g).app U).symm
    c.inv ≫ (pullback g').map
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit g'.toRingCatSheafHom =
      (pullback f').map (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit f'.toRingCatSheafHom  := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have hc := structureUnit_congr h
  have hc' := congrArg
    (fun q ↦ (pullbackCongr h).inv.app (SheafOfModules.unit S.ringCatSheaf) ≫ q) hc
  simp only [Iso.inv_hom_id_app_assoc] at hc'
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [structureUnit_comp]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc'.symm, structureUnit_comp]


end AlgebraicGeometry.Scheme.Modules
