/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageSectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import WeilConjectures.AlgebraicGeometry.Flat.FlatInvertibleCanonicalDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Bijectivity of the fixed section comparison

## References

* Stacks Project, Tag 0B91, clause (2), and Tag 079W
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The fixed degree-zero comparison is bijective after arbitrary base change. -/
theorem picardDirectImageSectionMap_bijective
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) {T : Scheme.{v}} (t : T ⟶ W) :
    Function.Bijective (picardDirectImageSectionMap f L W k t) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option maxRecDepth 2048 in
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let q := pullback.snd f k
  let p := pullback.snd f (t ≫ k)
  let M : (pullback f k).Modules := (Modules.tensorPullback (pullback.fst f k)).obj L
  let N : (pullback f (t ≫ k)).Modules := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let a : pullback f (t ≫ k) ⟶ pullback f k :=
    pullback.lift (pullback.fst f (t ≫ k)) (pullback.snd f (t ≫ k) ≫ t)
      (by rw [Category.assoc]; exact pullback.condition)
  have ha : a ≫ pullback.fst f k = pullback.fst f (t ≫ k) := pullback.lift_fst ..
  have hb : a ≫ pullback.snd f k = pullback.snd f (t ≫ k) ≫ t := pullback.lift_snd ..
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t ≫ k))))).symm
    (Modules.pushforwardComp a (pullback.fst f k) ≪≫ Modules.pushforwardCongr ha)
  let d : (Modules.pullback a).obj M ≅ N :=
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
  have hM : SheafOfModules.IsInvertible.{v, v, v} M := by
    let e := (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f k))).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (pullback.fst f k))
    have := Modules.IsInvertible.sheafOfModules_isInvertible
      ((Modules.pullback (pullback.fst f k)).obj L)
    exact SheafOfModules.IsInvertible.of_iso.{v, v, v} (e.app L).symm
  have sq : IsPullback a p q t := by
    apply IsPullback.of_right ?_ hb (IsPullback.of_hasPullback f k)
    simpa only [ha] using IsPullback.of_hasPullback f (t ≫ k)
  have hβ : IsIso (schemeDerivedBaseChangeMap q p t a hb
      ((DerivedCategory.singleFunctor _ 0).obj M)) :=
    Modules.isIso_derivedBaseChange_of_flat_invertible q t a p sq M
  have hc : IsIso (Modules.canonicalSinglePullbackMap a M) :=
    Modules.isIso_canonicalSinglePullbackMap a M
  let B : (derivedPullback t).obj ((schemeDerivedDirectImage q).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) ⟶
      (schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor _ 0).obj N) :=
    schemeDerivedBaseChangeMap (pullback.snd f k) (pullback.snd f (t ≫ k))
    t a hb ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (schemeDerivedDirectImage (pullback.snd f (t ≫ k))).map
        (Modules.canonicalSinglePullbackMap a M ≫
          (DerivedCategory.singleFunctor _ 0).map d.hom)
  let U := SheafOfModules.unit (moduleRings W.toRingedSpace)
  have hU : SheafOfModules.IsInvertible.{v, v, v} U := by
    dsimp [U]
    exact SheafOfModules.instIsInvertibleUnit.{v, v, v}
  let := hU
  have : IsIso (Modules.canonicalSinglePullbackMap t U) :=
    Modules.isIso_canonicalSinglePullbackMap t U
  let e := asIso (Modules.canonicalSinglePullbackMap t U) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit t.toRingCatSheafHom))
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0
  let z := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).app
      (SheafOfModules.unit (moduleRings T.toRingedSpace))
  let : IsGrothendieckAbelian.{v}
      (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  let : EnoughInjectives (pullback f (t ≫ k)).Modules :=
    by
      change EnoughInjectives
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace))
      exact IsGrothendieckAbelian.enoughInjectives.{v, v, v + 1}
  let : HasInjectiveResolutions (pullback f (t ≫ k)).Modules := inferInstance
  let r := Modules.canonicalDirectImageH0Iso (pullback.snd f (t ≫ k)) N
  have hB : IsIso B := by dsimp [B]; infer_instance
  have hGE : ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsGE 0 :=
    Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (RingedSpace.moduleDirectImage p.toLRSHom.toShHom) N
  let F := fun ξ ↦ e.inv ≫ ξ ≫ B
  have hF : Function.Bijective F :=
    (Iso.homCongr e (asIso B)).bijective
  have hH : Function.Bijective (fun ξ :
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
        (moduleRings T.toRingedSpace)) ⟶
      (schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor _ 0).obj N) ↦
        H.map ξ) := DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0
  have hm : Function.Bijective (fun ξ ↦ z.inv ≫ H.map (F ξ) ≫ r.hom) :=
    (Iso.homCongr z r).bijective.comp (hH.comp hF)
  have heval := (Modules.unitHomAddEquiv ((Modules.pushforward p).obj N)).bijective
  have hres : Function.Bijective (fun x : Γ(N, p ⁻¹ᵁ ⊤) ↦
      N.presheaf.map (homOfLE p.preimage_top.ge).op x) := by
    have : IsIso (homOfLE p.preimage_top.ge) :=
      ⟨⟨homOfLE p.preimage_top.le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (fun ξ ↦ N.presheaf.map
    (homOfLE p.preimage_top.ge).op
      ((z.inv ≫ H.map e.inv ≫ H.map ξ ≫ H.map B ≫ r.hom).val.app
        (Opposite.op ⊤) (1 : Γ(T, ⊤))))
  convert hres.comp (heval.comp hm) using 1
  funext ξ
  simp only [Function.comp_apply, F, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme
