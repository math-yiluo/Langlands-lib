/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Picard.HomotopySinglePullbackComposition
import WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit

/-! # Single-module comparison and composition of two pullbacks

Source: Stacks Project, Tag 0D5S, and the defining left-derived lift factorization.
(blueprint: lem-pc-canonical-single-pullback-composition).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullback Adjunction.leftAdjointUniq

local notation "dPullback" => AlgebraicGeometry.derivedPullback

private theorem paste
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ D) (Q : B ⥤ D)
    {y : D} {m n o : A} {b₀ b₁ b₂ b₃ b₄ : B}
    (a : L.obj m ⟶ y) (e : y ⟶ Q.obj b₁) (β : m ⟶ n)
    (δ : L.obj n ⟶ Q.obj b₀) (c : b₀ ⟶ b₁)
    (r : b₁ ⟶ b₄) (q : n ⟶ o) (δ' : L.obj o ⟶ Q.obj b₂)
    (t : b₀ ⟶ b₂) (s : b₂ ⟶ b₃) (p : b₃ ⟶ b₄)
    (hfac : a ≫ e = L.map β ≫ δ ≫ Q.map c)
    (ht : c ≫ r = t ≫ s ≫ p)
    (hn : L.map q ≫ δ' = δ ≫ Q.map t) :
    a ≫ (e ≫ Q.map r) = L.map (β ≫ q) ≫ (δ' ≫ Q.map s) ≫ Q.map p := by
  calc
    _ = (a ≫ e) ≫ Q.map r := (Category.assoc _ _ _).symm
    _ = (L.map β ≫ δ ≫ Q.map c) ≫ Q.map r := by rw [hfac]
    _ = L.map β ≫ δ ≫ Q.map (c ≫ r) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = L.map β ≫ δ ≫ Q.map (t ≫ s ≫ p) := by rw [ht]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun k ↦ L.map β ≫ k ≫ Q.map s ≫ Q.map p) hn.symm

private theorem fuse
    {A B : Type*} [Category A] [Category B] (Q : A ⥤ B)
    {x : B} {y z w : A} (e : x ⟶ Q.obj y) (a : y ⟶ z) (b : z ⟶ w) :
    e ≫ Q.map a ≫ Q.map b = e ≫ Q.map (a ≫ b) := by
  rw [Functor.map_comp]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem singleComparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    canonicalSinglePullbackMap f M =
      let := canonicalTensorPullbackAdditive f
      let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
      let t := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
        (pullbackPushforwardAdjunction f)
      ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex
              (tensorPullback f) (.up ℤ) 0).hom.app M) ≫
            (HomotopyCategory.singleFunctor _ 0).map (t.hom.app M)) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  simp only [canonicalSinglePullbackMap, cast_eq, Scheme.Modules, Scheme.ringCatSheaf,
    moduleRings, DerivedCategory.singleFunctor,
    DerivedCategory.singleFunctors, HomotopyCategory.singleFunctor,
    HomotopyCategory.singleFunctors, SingleFunctors.postcomp, Functor.comp_map,
    Functor.map_comp, Category.assoc, DerivedCategory.Qh,
    HomologicalComplexUpToQuasiIso.Qh, HomotopyCategory.quotient,
    Quotient.lift_map_functor_map, DerivedCategory.Q]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 200000 in
-- The selected derived counits have large dependent types.
/-- Compatibility with composition of two morphisms, before comparing square paths.
Source: Stacks Project, Tag 0D5S, and `Functor.leftDerived_fac_app` applied to the
factorization in `exists_derivedPullbackComposition`.
(blueprint: lem-pc-canonical-single-pullback-composition).

Proof: Write ε for the chosen derived counits and t for the unique left-adjoint
isomorphism from tensor pullback to ordinary pullback. Evaluate the defining
leftDerivedLift factorization at the single complex of N. Its right side is
Lf*(ε_g) followed by ε_f at the termwise g-pullback and the termwise tensor
composition isomorphism. Postcompose with the single-complex comparison for f ≫ g
and with the single embedding of t_(f ≫ g). Naturality of ε_f moves the
single-complex comparison for g through ε_f. Compatibility of the single-complex
isomorphisms with mapping a composite functor then identifies this with the two
successive single comparisons and the single embedding of tensor composition.
The remaining underived equation is
T_f(t_g) ≫ t_f ≫ pullbackComp.hom = tensorComp.hom ≫ t_(f ≫ g).
Apply the conjugate-morphism equivalence of the composite adjunctions: the
leftAdjointUniq counit equations make both sides the same pushforward composition
map, while conjugateEquiv_pullbackComp_inv pins its ordinary pullback mate.
Injectivity proves the underived equation, and mapping it by the single functor
finishes. No derived single comparison is inverted, so no flatness is required;
identity morphisms, zero modules, and empty schemes are included. -/
theorem canonicalSinglePullbackComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f g).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
      canonicalSinglePullbackMap (f ≫ g) N =
    (AlgebraicGeometry.derivedPullback f).map (canonicalSinglePullbackMap g N) ≫
      canonicalSinglePullbackMap f ((pullback g).obj N) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((pullbackComp f g).hom.app N) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let Q_X := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let Q_Y := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let Q_Z := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let E := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N
  let :=  (Classical.choose exists_derivedPullbackComposition.{u,w}) f
  let :=  (Classical.choose exists_derivedPullbackComposition.{u,w}) g
  let :=  (Classical.choose exists_derivedPullbackComposition.{u,w}) (f ≫ g)
  let C := (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w})))) f g
  let eps := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u,w})) (f ≫ g)
  have hfacC := perfectHomTensorCounit_comp f g E
  let ε_f := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u,w})) f
  let ε_g := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u,w})) g
  let t_f := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  let t_g := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  let t_fg := (Classical.choose (exists_tensorPullbackAdjunction (f ≫ g))).leftAdjointUniq
    (pullbackPushforwardAdjunction (f ≫ g))
  let r_f := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app ((pullback g).obj N)) ≫
    (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (t_f.hom.app ((pullback g).obj N))
  let r_g := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app N) ≫
    (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map (t_g.hom.app N)
  let r_fg := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorPullback (f ≫ g)) (ComplexShape.up ℤ) 0).hom.app N) ≫
    (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (t_fg.hom.app N)
  let T_f := (tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
  let T_g := (tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)
  let c := (Functor.mapHomotopyCategoryCompIso
    ((conjugateIsoEquiv
      (Classical.choose (exists_tensorPullbackAdjunction (f ≫ g)))
      ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
        (Classical.choose (exists_tensorPullbackAdjunction f)))).symm
      (pushforwardComp f g).symm) (ComplexShape.up ℤ)).hom.app E
  let p := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map ((pullbackComp f g).hom.app N)
  have ht : c ≫ r_fg = T_f.map r_g ≫ r_f ≫ p :=
    homotopySinglePullbackComposition f g N
  have hn := ε_f.naturality r_g
  change (dPullback f).map (Q_Y.map r_g) ≫
      ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj ((pullback g).obj N)) =
    ε_f.app (T_g.obj E) ≫ Q_X.map (T_f.map r_g) at hn
  change C.hom.app (Q_Z.obj E) ≫ eps.app E =
    (dPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
      Q_X.map c at hfacC
  have h : C.hom.app (Q_Z.obj E) ≫
      (eps.app E ≫ Q_X.map r_fg) =
    (dPullback f).map (ε_g.app E ≫ Q_Y.map r_g) ≫
      (ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj ((pullback g).obj N)) ≫
        Q_X.map r_f) ≫ Q_X.map p :=
    paste (dPullback f) Q_X _ _ _ _ _ _ _ _ _ _ _ hfacC ht hn
  have hfg : canonicalSinglePullbackMap (f ≫ g) N = eps.app E ≫ Q_X.map r_fg :=
    singleComparison_eq (f ≫ g) N
  have hg : canonicalSinglePullbackMap g N = ε_g.app E ≫ Q_Y.map r_g :=
    singleComparison_eq g N
  have hf : canonicalSinglePullbackMap f ((pullback g).obj N) =
      ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj ((pullback g).obj N)) ≫
        Q_X.map r_f := singleComparison_eq f ((pullback g).obj N)
  change C.hom.app (Q_Z.obj E) ≫ canonicalSinglePullbackMap (f ≫ g) N =
    (dPullback f).map (canonicalSinglePullbackMap g N) ≫
      canonicalSinglePullbackMap f ((pullback g).obj N) ≫ Q_X.map p
  exact (congrArg (fun k ↦ C.hom.app (Q_Z.obj E) ≫ k) hfg).trans
    (h.trans (congrArg₂ (fun kg kf ↦ (dPullback f).map kg ≫ kf ≫ Q_X.map p)
      hg.symm hf.symm))

end AlgebraicGeometry.Scheme.Modules
