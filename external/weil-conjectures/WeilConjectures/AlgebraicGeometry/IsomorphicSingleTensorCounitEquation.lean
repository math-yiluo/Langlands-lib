/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounitTransport
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
/-! # Counit equation for canonical transport
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-equation). -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback

private theorem single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N =
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
        (F.obj N) ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (c.hom.app N) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.singleMapHomologicalComplex,
    HomologicalComplex.single, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplex]

private theorem homotopy_single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor A 0).obj N) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N) =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N)) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
          (F.obj N)) ≫
      (HomotopyCategory.singleFunctor C 0).map (c.hom.app N) := by
  have hs := single_comp F G H c N
  have hq := congrArg
    (fun k ↦ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map k) hs
  simpa only [Functor.map_comp, Functor.mapHomotopyCategory_map,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctors, Functor.comp_map,
    Functor.comp_obj, Functor.mapHomotopyCategoryCompIso,
    Quotient.natIsoLift_hom, Functor.isoWhiskerRight_hom, Quotient.natTransLift,
    Functor.whiskerRight_app, HomotopyCategory.quotient_obj_as, Category.assoc] using hq

private def tensorAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)

private def tensorCompositionComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
  (conjugateIsoEquiv
    (tensorAdjunction (f ≫ g))
    ((tensorAdjunction g).comp
      (tensorAdjunction f))).symm
        (Scheme.Modules.pushforwardComp f g).symm

private def tensorCounit
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  pinnedPullbackCounit.{u, w} f

private theorem pinned_single_comp
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    let c := pinnedPullbackComposition.{u, w} f g
    let b := tensorCompositionComparison f g
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
        pinnedSingleTensorCounit (f ≫ g) 0 N =
      (derivedPullback f).map (pinnedSingleTensorCounit g 0 N) ≫
        pinnedSingleTensorCounit f 0 ((Scheme.Modules.tensorPullback g).obj N) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (b.hom.app N) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let Q_X := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let Q_Y := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let Q_Z := DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let E := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N
  let C := pinnedPullbackComposition.{u, w} f g
  let eps := tensorCounit.{u, w} (f ≫ g)
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)
  let : (derivedPullback (f ≫ g)).IsLeftDerivedFunctor eps W :=
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have hfac := (derivedPullback (f ≫ g)).leftDerived_fac_app eps W
    (derivedPullback g ⋙ derivedPullback f)
    ((Functor.associator DerivedCategory.Qh (derivedPullback g)
        (derivedPullback f)).inv ≫
      Functor.whiskerRight
        (tensorCounit.{u, w} g) (derivedPullback f) ≫
      (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
      Functor.whiskerLeft _
        (tensorCounit.{u, w} f) ≫
      (Functor.associator _ _
        (DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso
          ((conjugateIsoEquiv
            (tensorAdjunction (f ≫ g))
            ((tensorAdjunction g).comp
              (tensorAdjunction f))).symm
            (Scheme.Modules.pushforwardComp f g).symm)
          (ComplexShape.up ℤ)).hom
        (DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))) E
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp] at hfac
  have hfacC := (congrArg
    (fun α ↦ α.app (Q_Z.obj E) ≫ eps.app E) hc).trans hfac
  let ε_f := tensorCounit.{u, w} f
  let ε_g := tensorCounit.{u, w} g
  let b := tensorCompositionComparison f g
  let r_f := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback f) (ComplexShape.up ℤ) 0).hom.app
        ((Scheme.Modules.tensorPullback g).obj N))
  let r_g := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback g) (ComplexShape.up ℤ) 0).hom.app N)
  let r_fg := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback (f ≫ g)) (ComplexShape.up ℤ) 0).hom.app N)
  let T_f := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
  let T_g := (Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)
  let c := (Functor.mapHomotopyCategoryCompIso b (ComplexShape.up ℤ)).hom.app E
  let p := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (b.hom.app N)
  have ht : c ≫ r_fg = T_f.map r_g ≫ r_f ≫ p :=
    homotopy_single_comp _ _ _ b N
  have hn := ε_f.naturality r_g
  change (derivedPullback f).map (Q_Y.map r_g) ≫
      ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj N)) =
    ε_f.app (T_g.obj E) ≫ Q_X.map (T_f.map r_g) at hn
  change C.hom.app (Q_Z.obj E) ≫ eps.app E =
    (derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
      Q_X.map c at hfacC
  have h : C.hom.app (Q_Z.obj E) ≫ (eps.app E ≫ Q_X.map r_fg) =
    (derivedPullback f).map (ε_g.app E ≫ Q_Y.map r_g) ≫
      (ε_f.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj N)) ≫ Q_X.map r_f) ≫ Q_X.map p := by
    calc
      _ = (C.hom.app (Q_Z.obj E) ≫ eps.app E) ≫ Q_X.map r_fg :=
        (Category.assoc _ _ _).symm
      _ = ((derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
          Q_X.map c) ≫ Q_X.map r_fg :=
        congrArg (fun k ↦ k ≫ Q_X.map r_fg) hfacC
      _ = (derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
          Q_X.map (c ≫ r_fg) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (derivedPullback f).map (ε_g.app E) ≫ ε_f.app (T_g.obj E) ≫
          Q_X.map (T_f.map r_g ≫ r_f ≫ p) :=
        congrArg (fun k ↦ (derivedPullback f).map (ε_g.app E) ≫
          ε_f.app (T_g.obj E) ≫ Q_X.map k) ht
      _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (derivedPullback f).map (ε_g.app E) ≫
            k ≫ Q_X.map r_f ≫ Q_X.map p) hn.symm
  with_unfolding_all
    simp only [pinnedSingleTensorCounit, cast_eq, pinnedPullbackCounit, r_f, r_g, r_fg,
      p, E, C, eps, ε_f, ε_g, tensorCounit, Q_X, Q_Y, Q_Z, DerivedCategory.singleFunctor,
      DerivedCategory.singleFunctors, SingleFunctors.postcomp, Functor.map_comp,
      Functor.comp_map, Functor.comp_obj, Category.assoc] at h ⊢
    exact h
private theorem transport_eq
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {K B : C} {A : D} (q : K ⟶ B) (r : L.obj B ⟶ A) (t : R.obj A ≅ B)
    (ht : t.inv = a.unit.app B ≫ R.map r) :
    a.unit.app K ≫ R.map (L.map q ≫ r) ≫ t.hom = q := by
  simp only [R.map_comp, ← Category.assoc]
  rw [a.unit_naturality q]
  rw [Category.assoc q (a.unit.app B) (R.map r), ← ht]
  simp only [Category.assoc, t.inv_hom_id, Category.comp_id]


private theorem single_tensor_transport_equation
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X P Z : Scheme.{u}} (p : P ⟶ X) (e : Z ≅ P)
    (a : derivedPullback e.hom ⊣ schemeDerivedDirectImage e.hom)
    (t : (Scheme.Modules.tensorPullback (e.hom ≫ p) ⋙
      DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0) ⋙
      schemeDerivedDirectImage e.hom ≅
      Scheme.Modules.tensorPullback p ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0)
    (ht : ∀ M : X.Modules,
      t.inv.app M = a.unit.app ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback p).obj M)) ≫
        (schemeDerivedDirectImage e.hom).map
          (pinnedSingleTensorCounit e.hom 0 ((Scheme.Modules.tensorPullback p).obj M) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).map
                ((tensorCompositionComparison e.hom p).hom.app M))) :
    ∀ M : X.Modules,
      (a.unit.app ((derivedPullback p).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))) ≫
        (schemeDerivedDirectImage e.hom).map
          ((pinnedPullbackComposition e.hom p).hom.app ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
              pinnedSingleTensorCounit (e.hom ≫ p) 0 M) ≫ t.hom.app M =
        pinnedSingleTensorCounit p 0 M := by
  intro M
  rw [pinned_single_comp e.hom p M]
  exact transport_eq a (pinnedSingleTensorCounit p 0 M)
    (pinnedSingleTensorCounit e.hom 0 ((Scheme.Modules.tensorPullback p).obj M) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).map
          ((tensorCompositionComparison e.hom p).hom.app M)) (t.app M) (ht M)


/-- The canonical transported isomorphism satisfies the counit equation.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-isomorphic-single-tensor-counit-equation).
Proof: transpose the composition-pinned counit through the adjunction of the
isomorphism. Use the inverse-component formula in the transport theorem:
it is the unit at (p^*M)[0] followed by direct image of the single tensor
counit for e and the underived tensor composition comparison. Naturality
of this unit moves the counit for p across it. The defining left-derived
composition factorization then identifies the direct-image term with
c(e,p) followed by the counit for e p. Thus the first two factors in the
displayed equation equal the counit for p followed by t.inv.app M.
Compose with t.hom.app M and cancel by the inverse identity. This argument
uses the pinned comparisons and includes zero modules and empty schemes;
it would not apply to an arbitrary natural isomorphism. -/
theorem isomorphic_single_tensor_counit_transport_equation
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X P Z : Scheme.{u}} (p : P ⟶ X) (e : Z ≅ P) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction s
        (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) s))
    let t := Classical.choose (exists_isomorphic_single_tensor_counit_transport p e)
    ∀ M : X.Modules,
      let K := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
      (a e.hom).unit.app ((derivedPullback p).obj K) ≫
          (schemeDerivedDirectImage e.hom).map
            ((c e.hom p).hom.app K ≫ pinnedSingleTensorCounit (e.hom ≫ p) 0 M) ≫
          t.hom.app M = pinnedSingleTensorCounit p 0 M := by
  intro c a t M K
  exact single_tensor_transport_equation p e (a e.hom) t
    (Classical.choose_spec (exists_isomorphic_single_tensor_counit_transport p e)) M
end AlgebraicGeometry
