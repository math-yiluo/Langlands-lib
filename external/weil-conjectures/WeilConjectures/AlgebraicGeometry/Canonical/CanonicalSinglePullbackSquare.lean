/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSinglePullbackComposition
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorSinglePullbackComposition

/-! # Pullback composition compatibility on single modules

Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-canonical-single-pullback-square).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem singlePullback_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    let := Scheme.Modules.canonicalTensorPullbackAdditive f
    let ε := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) f
    let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)
    let Q := DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let H := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let s := HomologicalComplex.singleMapHomologicalComplex
      (W₁ := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (W₂ := SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (Scheme.Modules.tensorPullback f) (ComplexShape.up ℤ) 0
    let SA := DerivedCategory.singleFunctor.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let SB := DerivedCategory.singleFunctor.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
    let HA := HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let T := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
    have he := ε.naturality (HA.map a)
    change (AlgebraicGeometry.derivedPullback f).map (SA.map a) ≫ ε.app (HA.obj N) =
      ε.app (HA.obj M) ≫ Q.map (T.map (HA.map a)) at he
    have hs := congrArg (fun k ↦ Q.map (H.map k)) (s.hom.naturality a)
    simp only [Functor.map_comp, Functor.comp_map] at hs
    change Q.map (T.map (HA.map a)) ≫ Q.map (H.map (s.hom.app N)) =
      Q.map (H.map (s.hom.app M)) ≫ SB.map ((Scheme.Modules.tensorPullback f).map a) at hs
    have ht := congrArg (fun k ↦ SB.map k) (t.hom.naturality a)
    simp only [Functor.map_comp] at ht
    simpa only [canonicalSinglePullbackMap, cast_eq, Category.assoc,
      ε, t, Q, H, s, SA, SB, HA, T, Scheme.Modules, Scheme.ringCatSheaf,
      moduleRings] using AlgebraicGeometry.naturality_three
      ((AlgebraicGeometry.derivedPullback f).map (SA.map a)) (Q.map (T.map (HA.map a)))
      (SB.map ((Scheme.Modules.tensorPullback f).map a))
      (SB.map ((Scheme.Modules.pullback f).map a))
      (ε.app (HA.obj M)) (Q.map (H.map (s.hom.app M))) (SB.map (t.hom.app M))
      (ε.app (HA.obj N)) (Q.map (H.map (s.hom.app N))) (SB.map (t.hom.app N)) he hs ht

private theorem singlePullback_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (N : Y.Modules) :
    eqToHom (congrArg (fun k ↦ (AlgebraicGeometry.derivedPullback k).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj N)) h.symm) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap g N ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((pullbackCongr h).inv.app N) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    subst g
    simp [pullbackCongr]

/-- Single pullback comparisons respect a commutative square and a module morphism.
This concerns only pullback; it involves neither base change nor direct image.
Source: Stacks Project, Tag 0D5S, and the naturality of left-derived counits.
(blueprint: lem-pc-canonical-single-pullback-square).

Proof: Evaluate the defining `leftDerivedLift` factorization for the selected
composition isomorphisms on N[0]. It identifies successive left-derived counits
with the counit for the composite followed by underived tensor composition.
Apply this identity to (f', g) and (g', f), transport along h, and cancel the
invertible derived composition comparison to obtain the square for N.
Transport tensor pullback to ordinary pullback by the unique left-adjoint
isomorphisms. Their counit laws identify tensor composition, defined as the mate
of pushforward composition, with `pullbackComp`; transport along h becomes
`pullbackCongr h`. Thus the ordinary square comparison is c.inv. Finally,
naturality of the left-derived counit and of the single-map comparisons for the
morphism a moves a across the g' comparison, yielding the displayed formula.
No comparison on a single module is inverted. The argument covers h reflexive,
identity morphisms, zero a, zero modules and empty schemes without extra assumptions. -/
theorem canonicalSinglePullbackSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g) (N : S.Modules) (M : X.Modules)
    (a : (pullback f).obj N ⟶ M) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N
    let c := (pullbackComp g' f).app N ≪≫ (pullbackCongr h).app N ≪≫
      ((pullbackComp f' g).app N).symm
    let d := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app E ≫
      eqToHom (congrArg (fun k ↦ (AlgebraicGeometry.derivedPullback k).obj E) h.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app E
    d ≫ (AlgebraicGeometry.derivedPullback g').map
        (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
        canonicalSinglePullbackMap g' M =
      (AlgebraicGeometry.derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
            (c.inv ≫ (pullback g').map a) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    classical
    dsimp only
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N
    let H := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0
    let C := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) g' f
    let C' := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f' g
    let e := eqToHom (congrArg (fun k ↦ (AlgebraicGeometry.derivedPullback k).obj E) h.symm)
    let b := (pullbackComp g' f).app N
    let b' := (pullbackComp f' g).app N
    let t := (pullbackCongr h).app N
    have hi : C.inv.app E ≫
        (AlgebraicGeometry.derivedPullback g').map (canonicalSinglePullbackMap f N) ≫
        canonicalSinglePullbackMap g' ((pullback f).obj N) =
      canonicalSinglePullbackMap (g' ≫ f) N ≫ H.map b.inv := by
      have hc := canonicalSinglePullbackComposition g' f N
      change C.hom.app E ≫ canonicalSinglePullbackMap (g' ≫ f) N =
        (AlgebraicGeometry.derivedPullback g').map (canonicalSinglePullbackMap f N) ≫
          canonicalSinglePullbackMap g' ((pullback f).obj N) ≫ H.map b.hom at hc
      have hc' := congrArg (fun k ↦ C.inv.app E ≫ k ≫ H.map b.inv) hc
      have hb : H.map (b.hom ≫ b.inv) = 𝟙 _ :=
        (congrArg H.map b.hom_inv_id).trans (H.map_id _)
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp, hb] at hc'
      have hc'' := hc'.symm
      simp only [← Category.assoc] at hc''
      simpa only [Category.assoc] using (Category.comp_id _).symm.trans hc''
    have ht := singlePullback_congr h N
    change e ≫ canonicalSinglePullbackMap (g' ≫ f) N =
      canonicalSinglePullbackMap (f' ≫ g) N ≫ H.map t.inv at ht
    have hc := canonicalSinglePullbackComposition f' g N
    change C'.hom.app E ≫ canonicalSinglePullbackMap (f' ≫ g) N =
      (AlgebraicGeometry.derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫ H.map b'.hom at hc
    have hs : (C'.hom.app E ≫ e ≫ C.inv.app E) ≫
        (AlgebraicGeometry.derivedPullback g').map (canonicalSinglePullbackMap f N) ≫
        canonicalSinglePullbackMap g' ((pullback f).obj N) =
      (AlgebraicGeometry.derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫
        H.map (b'.hom ≫ t.inv ≫ b.inv) := by
      calc
        _ = C'.hom.app E ≫ e ≫
            (canonicalSinglePullbackMap (g' ≫ f) N ≫ H.map b.inv) := by
              simpa only [Category.assoc] using
                congrArg (fun k ↦ C'.hom.app E ≫ e ≫ k) hi
        _ = C'.hom.app E ≫ canonicalSinglePullbackMap (f' ≫ g) N ≫
            H.map t.inv ≫ H.map b.inv := by
              simpa only [Category.assoc] using
                congrArg (fun k ↦ C'.hom.app E ≫ k ≫ H.map b.inv) ht
        _ = _ := by
          simpa only [Functor.map_comp, Category.assoc] using
            congrArg (fun k ↦ k ≫ H.map t.inv ≫ H.map b.inv) hc
    have hn := singlePullback_naturality g' a
    change (AlgebraicGeometry.derivedPullback g').map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
        canonicalSinglePullbackMap g' M =
      canonicalSinglePullbackMap g' ((pullback f).obj N) ≫
        H.map ((pullback g').map a) at hn
    change (C'.hom.app E ≫ e ≫ C.inv.app E) ≫
        (AlgebraicGeometry.derivedPullback g').map (canonicalSinglePullbackMap f N ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
        canonicalSinglePullbackMap g' M =
      (AlgebraicGeometry.derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫
        H.map (((b ≪≫ t ≪≫ b'.symm).inv) ≫ (pullback g').map a)
    calc
      _ = ((C'.hom.app E ≫ e ≫ C.inv.app E) ≫
            (AlgebraicGeometry.derivedPullback g').map (canonicalSinglePullbackMap f N) ≫
            canonicalSinglePullbackMap g' ((pullback f).obj N)) ≫
          H.map ((pullback g').map a) := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k ↦ (C'.hom.app E ≫ e ≫ C.inv.app E) ≫
            (AlgebraicGeometry.derivedPullback g').map (canonicalSinglePullbackMap f N) ≫ k) hn
      _ = _ := by
        rw [hs]
        simp only [Iso.trans_inv, Iso.symm_inv, ← Functor.map_comp,
          Category.assoc]

end AlgebraicGeometry.Scheme.Modules
