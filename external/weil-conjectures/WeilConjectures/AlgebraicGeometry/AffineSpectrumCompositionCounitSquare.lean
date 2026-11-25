/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Counit square for affine spectrum pullback composition

Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-affine-spectrum-composition-counit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforwardCongr (rfl : f = f) = Iso.refl _ := by
  ext M U
  simp

private theorem tensor_composition_inv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).inv =
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm).hom := by
  unfold Scheme.Modules.tensorPullbackCompositionIso
  rw [pushforwardCongr_refl]
  rfl

private theorem tensor_composition_symm
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).symm =
      (conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm :=
  Iso.ext (tensor_composition_inv f g)

private theorem map_complex_comparison
    {V W D : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
    [Category D] {F G H : V ⥤ W}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (a : F ≅ G) (b : F ≅ H)
    (Q : CochainComplex W ℤ ⥤ D) (P : CochainComplex V ℤ) :
    Q.map ((NatIso.mapHomologicalComplex (a.symm ≪≫ b) (.up ℤ)).hom.app P) =
      (Q.mapIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)).inv ≫
        (Q.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app P)).hom := by
  change Q.map ((NatTrans.mapHomologicalComplex (a.inv ≫ b.hom) (.up ℤ)).app P) = _
  rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Q.map_comp]
  rfl

private theorem reassoc_factorization
    {C : Type*} [Category C] {U V A B D : C}
    (c : U ≅ V) (ε : V ⟶ A) (l : U ⟶ B) (r : B ⟶ D) (t : D ⟶ A)
    (h : c.hom ≫ 𝟙 V ≫ ε = l ≫ r ≫ t) : c.hom ≫ ε = (l ≫ r) ≫ t := by
  simpa only [Category.id_comp, Category.assoc] using h

private theorem reassoc_transported_factorization
    {C : Type*} [Category C] {U V V' A B D : C}
    (c : U ≅ V) (e : V ≅ V') (ε : V' ⟶ A)
    (l : U ⟶ B) (r : B ⟶ D) (t : D ⟶ A)
    (h : c.hom ≫ e.hom ≫ ε = l ≫ r ≫ t) :
    (c ≪≫ e).hom ≫ ε = (l ≫ r) ≫ t :=
  (Category.assoc c.hom e.hom ε).trans (h.trans (Category.assoc l r t).symm)

private theorem eqToIso_congr_symm_private
    {C D : Type*} [Category D] (F : C → D) {k l : C} (h : k = l) :
    eqToIso (congrArg F h.symm) = (eqToIso (congrArg F h)).symm := by
  subst l
  rfl

/-- Public export of the private `eqToIso_congr_symm_private`
(used by `import all` importers; linter.privateModule). -/
alias eqToIso_congr_symm := eqToIso_congr_symm_private

private theorem compare_counit_factorizations_private
    {C : Type*} [Category C] {U V W A B D : C}
    (c₁ : U ≅ V) (c₂ : W ≅ V) (b₁ : A ≅ B) (b₂ : A ≅ D)
    (ε : V ⟶ A) (l : U ⟶ B) (r : W ⟶ D)
    (h₁ : c₁.hom ≫ ε = l ≫ b₁.inv) (h₂ : c₂.hom ≫ ε = r ≫ b₂.inv) :
    l ≫ b₁.inv ≫ b₂.hom = c₁.hom ≫ c₂.inv ≫ r := by
  have hr : r = c₂.hom ≫ ε ≫ b₂.hom := by
    rw [← Category.assoc, h₂, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [Iso.inv_hom_id_assoc]
  exact ((reassoc_of% h₁) b₂.hom).symm

/-- Public export of the private `compare_counit_factorizations_private`
(used by `import all` importers; linter.privateModule). -/
alias compare_counit_factorizations := compare_counit_factorizations_private

noncomputable def selectedComposition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback.{u, w} g ⋙ derivedPullback.{u, w} f ≅ derivedPullback.{u, w} (f ≫ g) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f g

private theorem composition_factorization_private
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    (selectedComposition.{u, w} f g).hom.app (DerivedCategory.Q.{w}.obj P) ≫
        (counit (f ≫ g)).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      ((derivedPullback.{u, w} f).map
          ((counit g).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (counit f).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))) ≫
        (DerivedCategory.Q.{w}.mapIso
          ((NatIso.mapHomologicalComplex
            (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl)
            (.up ℤ)).app P)).inv := by
  have : (derivedPullback.{u, w} (f ≫ g)).IsLeftDerivedFunctor (counit (f ≫ g))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  let β := (Functor.associator DerivedCategory.Qh.{w} (derivedPullback.{u, w} g)
      (derivedPullback.{u, w} f)).inv ≫
    Functor.whiskerRight (counit g) (derivedPullback.{u, w} f) ≫
    (Functor.associator _ DerivedCategory.Qh.{w} (derivedPullback.{u, w} f)).hom ≫
    Functor.whiskerLeft _ (counit f) ≫
    (Functor.associator _ _
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        ((conjugateIsoEquiv
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
          (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)).hom
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  have hnat : Functor.whiskerLeft DerivedCategory.Qh.{w} (selectedComposition.{u, w} f g).hom ≫
      counit (f ≫ g) = β := by
    rw [show (selectedComposition.{u, w} f g).hom = _ from hc]
    exact Functor.leftDerived_fac (derivedPullback.{u, w} (f ≫ g)) (counit (f ≫ g))
      (HomotopyCategory.quasiIso _ (.up ℤ)) (derivedPullback.{u, w} g ⋙ derivedPullback.{u, w} f) β
  have h := congrArg (fun t ↦ t.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) hnat
  dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app] at h
  simp only [Category.id_comp] at h
  rw [← tensor_composition_symm f g] at h
  have hmap : (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
      ((Functor.mapHomotopyCategoryCompIso
          (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).symm
          (.up ℤ)).hom.app ((HomotopyCategory.quotient
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj P)) =
      ((DerivedCategory.Q.{w}
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).mapIso
        ((NatIso.mapHomologicalComplex
          (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl) (.up ℤ)).app P)).inv := by
    rfl
  erw [hmap] at h
  simp only [Functor.comp_obj, Category.assoc] at h ⊢
  exact h

/-- Public export of the private `composition_factorization_private`
(used by `import all` importers; linter.privateModule). -/
alias composition_factorization := composition_factorization_private

private theorem composition_factorization_transport_private
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    ((selectedComposition.{u, w} f g ≪≫
        eqToIso (congrArg (fun l ↦ derivedPullback.{u, w} l) h)).app
          (DerivedCategory.Q.{w}.obj P)).hom ≫
        (counit k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      ((derivedPullback.{u, w} f).map
          ((counit g).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (counit f).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))) ≫
        (DerivedCategory.Q.{w}.mapIso
          ((NatIso.mapHomologicalComplex
            (Scheme.Modules.tensorPullbackCompositionIso f g k h) (.up ℤ)).app P)).inv := by
  cases h
  simpa only [eqToIso_refl, Iso.trans_refl, Iso.app_hom] using
    composition_factorization_private f g P

/-- Public export of the private `composition_factorization_transport_private`
(used by `import all` importers; linter.privateModule). -/
alias composition_factorization_transport := composition_factorization_transport_private
/-- The composition comparison intertwines the successive derived counits at a complex.
There is no coefficient morphism, representative isomorphism or K-flatness assumption.
Source: Stacks Project, Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-pc-affine-spectrum-composition-counit-square).

Proof: Apply the leftDerived_fac_app equation to each of the two chosen composition
comparisons, at the image of P in the homotopy category. Expand whiskering and
associators: each equation is the composite of the two successive counits followed
by Qh of the underived composition comparison. The latter is the inverse of the
pinned tensorPullbackCompositionIso, since conjugation commutes with inversion and
pushforwardCongr rfl is the identity. Transport the second equation along
isoSpec_inv_naturality. Its total pullback and counit agree with those in the first
equation by equality elimination and proof irrelevance. Cancel the second derived
comparison and the first underived comparison. The resulting square is precisely
the displayed equation. The quotient/localization comparison has identity components;
its naturality identifies Qh of the termwise comparison with Q of that comparison.
No inversion of a counit is used; zero complexes and empty schemes satisfy the same
factorization equations. -/
private theorem affineSpectrum_composition_counit_square_aux
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
      (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
    (derivedPullback (Spec.map g'.appTop)).map
        ((counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
    (affineSpectrumDerivedPullbackIso g').hom.app (DerivedCategory.Q.obj P) ≫
      (derivedPullback X'.isoSpec.inv).map
        ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (counit X'.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) := by
  let b₁ := Scheme.Modules.tensorPullbackCompositionIso
    (Spec.map g'.appTop) X.isoSpec.inv ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl
  let b₂ := Scheme.Modules.tensorPullbackCompositionIso
    X'.isoSpec.inv g' ((Spec.map g'.appTop) ≫ X.isoSpec.inv)
    (Scheme.isoSpec_inv_naturality g').symm
  let c₁ := selectedComposition.{u, w} (Spec.map g'.appTop) X.isoSpec.inv
  let c₂ := selectedComposition.{u, w} X'.isoSpec.inv g' ≪≫
    (eqToIso (congrArg (fun k ↦ derivedPullback.{u, w} k)
      (Scheme.isoSpec_inv_naturality g'))).symm
  have h₁ := composition_factorization_private (Spec.map g'.appTop) X.isoSpec.inv P
  have h₂ := composition_factorization_transport_private X'.isoSpec.inv g'
    ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm P
  erw [eqToIso_congr_symm_private (fun k ↦ derivedPullback.{u, w} k)
    (Scheme.isoSpec_inv_naturality g')] at h₂
  have h := compare_counit_factorizations_private
    (c₁.app (DerivedCategory.Q.obj P)) (c₂.app (DerivedCategory.Q.obj P))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b₁ (.up ℤ)).app P))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b₂ (.up ℤ)).app P))
    ((counit ((Spec.map g'.appTop) ≫ X.isoSpec.inv)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) _ _ h₁ h₂
  dsimp only
  have he : affineSpectrumDerivedPullbackIso g' = c₁ ≪≫ c₂.symm := by
    dsimp only [affineSpectrumDerivedPullbackIso, c₁, c₂, selectedComposition]
    simp only [Iso.trans_symm, Iso.symm_symm_eq]
  conv_rhs => rw [he]
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Functor.map_comp,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using h


/-- The composition comparison intertwines the successive derived counits at a complex.
There is no coefficient morphism, representative isomorphism or K-flatness assumption.
Source: Stacks Project, Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-pc-affine-spectrum-composition-counit-square).

Proof: Apply the leftDerived_fac_app equation to each of the two chosen composition
comparisons, at the image of P in the homotopy category. Expand whiskering and
associators: each equation is the composite of the two successive counits followed
by Qh of the underived composition comparison. The latter is the inverse of the
pinned tensorPullbackCompositionIso, since conjugation commutes with inversion and
pushforwardCongr rfl is the identity. Transport the second equation along
isoSpec_inv_naturality. Its total pullback and counit agree with those in the first
equation by equality elimination and proof irrelevance. Cancel the second derived
comparison and the first underived comparison. The resulting square is precisely
the displayed equation. The quotient/localization comparison has identity components;
its naturality identifies Qh of the termwise comparison with Q of that comparison.
No inversion of a counit is used; zero complexes and empty schemes satisfy the same
factorization equations. -/
theorem affineSpectrum_composition_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
      (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
    (derivedPullback (Spec.map g'.appTop)).map
        (cast (by rfl)
          ((counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :
          (derivedPullback X.isoSpec.inv).obj (DerivedCategory.Q.obj P) ⟶
            DerivedCategory.Q.obj
              (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
                (.up ℤ)).obj P)) ≫
      cast (by rfl) ((counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P))) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
    (affineSpectrumDerivedPullbackIso g').hom.app (DerivedCategory.Q.obj P) ≫
      (derivedPullback X'.isoSpec.inv).map
        (cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :
          (derivedPullback g').obj (DerivedCategory.Q.obj P) ⟶
            DerivedCategory.Q.obj
              (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) ≫
      cast (by rfl) ((counit X'.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P))) := by
  with_unfolding_all
    exact affineSpectrum_composition_counit_square_aux g' P

end AlgebraicGeometry.SingleComplexBaseChange

