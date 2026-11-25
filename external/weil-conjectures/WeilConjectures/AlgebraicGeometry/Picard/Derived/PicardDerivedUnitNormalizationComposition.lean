/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSinglePullbackComposition
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorSinglePullbackComposition

/-! # Composition of derived structure-sheaf normalization

## References

* Stacks Project, Tag 0D5S and Tag 08HY
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [hD : ∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

namespace Modules

attribute [local irreducible] tensorPullback Adjunction.leftAdjointUniq

omit hD in
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

private theorem singlePullback_naturality
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a) := by
  exact AlgebraicGeometry.single_naturality f a

end Modules

/-- The derived structure-sheaf normalization, with its actual unit comparisons. -/
@[irreducible]
def picardDerivedUnitNormalization (W : Scheme.{v}) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback r).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings V.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings V.toRingedSpace)) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let U := SheafOfModules.unit (moduleRings W.toRingedSpace)
    letI : SheafOfModules.IsInvertible.{v, v, v} U :=
      SheafOfModules.instIsInvertibleUnit.{v, v, v}
    letI : IsIso (Modules.canonicalSinglePullbackMap r U) :=
      Modules.isIso_canonicalSinglePullbackMap r U
    exact asIso (Modules.canonicalSinglePullbackMap r U) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (asIso (SheafOfModules.pullbackObjUnitToUnit r.toRingCatSheafHom))

/-- Derived structure-sheaf normalization respects composition of base maps.
There is no direct image, coefficient module, fibre product or test section. -/
theorem picardDerivedUnitNormalization_comp
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (h : i ≫ t = t') :
  let e : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback r).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings V.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings V.toRingedSpace)) :=
    picardDerivedUnitNormalization W
  let C := canonicalDerivedPullbackComposition i t ≪≫
    eqToIso (congrArg (fun q : T' ⟶ W ↦ derivedPullback q) h)
  let U := SheafOfModules.unit (moduleRings T.toRingedSpace)
  (derivedPullback i).map (e t).inv ≫ C.hom.app _ =
    Modules.canonicalSinglePullbackMap i U ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).map
          (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom) ≫ (e t').inv := by
  classical
  intro e C U
  subst t'
  let OW := SheafOfModules.unit (moduleRings W.toRingedSpace)
  let O := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj OW
  let H := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0
  let s := Modules.canonicalSinglePullbackMap i U ≫
    H.map (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)
  let u := SheafOfModules.pullbackObjUnitToUnit t.toRingCatSheafHom
  have hc := Modules.canonicalSinglePullbackComposition i t OW
  have hn := Modules.singlePullback_naturality i u
  have hu := Modules.structureUnit_comp i t
  have he : (derivedPullback i).map (e t).hom ≫ s =
      C.hom.app O ≫ (e (i ≫ t)).hom := by
    dsimp only [e, s, C]
    unfold picardDerivedUnitNormalization
    simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      eqToIso_refl, Iso.refl_hom,
      Category.comp_id]
    change (derivedPullback i).map
        (Modules.canonicalSinglePullbackMap t OW ≫
          (DerivedCategory.singleFunctor _ 0).map u) ≫
        Modules.canonicalSinglePullbackMap i U ≫
          H.map (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom) =
      (canonicalDerivedPullbackComposition i t).hom.app O ≫
        Modules.canonicalSinglePullbackMap (i ≫ t) OW ≫
          H.map (SheafOfModules.pullbackObjUnitToUnit (i ≫ t).toRingCatSheafHom)
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((derivedPullback i).map ((DerivedCategory.singleFunctor _ 0).map u))]
    rw [hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp, hu, Functor.map_comp]
    simp only [← Category.assoc]
    simpa only [Category.assoc, canonicalDerivedPullbackComposition, OW, O, H,
      Scheme.Modules, Scheme.ringCatSheaf, Modules.pullback, moduleRings] using
      congrArg (fun q ↦ q ≫
        H.map (SheafOfModules.pullbackObjUnitToUnit (i ≫ t).toRingCatSheafHom)) hc.symm
  have he' := congrArg (fun q ↦ (derivedPullback i).map (e t).inv ≫
    q ≫ (e (i ≫ t)).inv) he
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Iso.hom_inv_id, Category.comp_id] at he'
  erw [(derivedPullback i).map_id] at he'
  simpa only [Category.id_comp, Category.assoc, O, s, H] using he'.symm

end
end AlgebraicGeometry.Scheme
