/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Tensor pullback square and conjugation

Source: Stacks Project, Tags 0095, 0096, 0097 and 08HY.
(blueprint: lem-sc-picard-tensor-square-conjugacy)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_conjugate {X Y : Scheme.{u}} (k : X ⟶ Y) :
    conjugateEquiv (pullbackPushforwardAdjunction k)
      (Classical.choose (exists_tensorPullbackAdjunction k))
      (picardTensorComparison k).hom = 𝟙 (pushforward k) := by
  simp [picardTensorComparison, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv_symm_apply_inv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_inv_conjugate {X Y : Scheme.{u}} (k : X ⟶ Y) :
    conjugateEquiv (Classical.choose (exists_tensorPullbackAdjunction k))
      (pullbackPushforwardAdjunction k)
      (picardTensorComparison k).inv = 𝟙 (pushforward k) := by
  simp [picardTensorComparison, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv_symm_apply_hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorComp {X Y Z : Scheme.{u}} (k : X ⟶ Y) (l : Y ⟶ Z) :
    tensorPullback l ⋙ tensorPullback k ≅ tensorPullback (k ≫ l) :=
  Functor.isoWhiskerRight (picardTensorComparison l) (tensorPullback k) ≪≫
    Functor.isoWhiskerLeft (pullback l) (picardTensorComparison k) ≪≫
      pullbackComp k l ≪≫ (picardTensorComparison (k ≫ l)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComp_app {X Y Z : Scheme.{u}} (k : X ⟶ Y) (l : Y ⟶ Z)
    (A : Z.Modules) : (tensorComp k l).app A = picardTensorCompIso k l A := by
  rfl

-- Matching the whiskering laws unfolds the scheme module category instances.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComp_inv_conjugate {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (l : Y ⟶ Z) :
    conjugateEquiv
      ((Classical.choose (exists_tensorPullbackAdjunction l)).comp
        (Classical.choose (exists_tensorPullbackAdjunction k)))
      (Classical.choose (exists_tensorPullbackAdjunction (k ≫ l)))
      (tensorComp k l).inv = (pushforwardComp k l).hom := by
  dsimp only [tensorComp, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction l).comp
      (Classical.choose (exists_tensorPullbackAdjunction k)))]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction l).comp (pullbackPushforwardAdjunction k))]
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (k ≫ l))]
  rw [comparison_conjugate, conjugateEquiv_pullbackComp_inv]
  rw [conjugateEquiv_whiskerLeft
    (Classical.choose (exists_tensorPullbackAdjunction k))
    (pullbackPushforwardAdjunction k) (pullbackPushforwardAdjunction l)]
  rw [conjugateEquiv_whiskerRight
    (Classical.choose (exists_tensorPullbackAdjunction l))
    (pullbackPushforwardAdjunction l)
    (Classical.choose (exists_tensorPullbackAdjunction k))]
  rw [comparison_inv_conjugate, comparison_inv_conjugate]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComp_inv_mate {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (l : Y ⟶ Z) :
    (conjugateEquiv
      ((Classical.choose (exists_tensorPullbackAdjunction l)).comp
        (Classical.choose (exists_tensorPullbackAdjunction k)))
      (Classical.choose (exists_tensorPullbackAdjunction (k ≫ l)))).symm
      (pushforwardComp k l).hom = (tensorComp k l).inv := by
  rw [← tensorComp_inv_conjugate]
  exact Equiv.symm_apply_apply _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComp_hom_mate {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (l : Y ⟶ Z) :
    (conjugateEquiv
      (Classical.choose (exists_tensorPullbackAdjunction (k ≫ l)))
      ((Classical.choose (exists_tensorPullbackAdjunction l)).comp
        (Classical.choose (exists_tensorPullbackAdjunction k)))).symm
      (pushforwardComp k l).inv = (tensorComp k l).hom := by
  have hi : conjugateIsoEquiv
      ((Classical.choose (exists_tensorPullbackAdjunction l)).comp
        (Classical.choose (exists_tensorPullbackAdjunction k)))
      (Classical.choose (exists_tensorPullbackAdjunction (k ≫ l)))
      (tensorComp k l).symm = pushforwardComp k l := by
    apply Iso.ext
    exact tensorComp_inv_conjugate k l
  have hh := congrArg Iso.inv hi
  rw [← hh]
  exact Equiv.symm_apply_apply _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem equality_mate {X Y : Scheme.{u}} (k l : X ⟶ Y) (e : k = l) :
    (conjugateEquiv (Classical.choose (exists_tensorPullbackAdjunction k))
      (Classical.choose (exists_tensorPullbackAdjunction l))).symm
      (pushforwardCongr e).hom =
        eqToHom (congrArg tensorPullback e.symm) := by
  subst l
  have he : (pushforwardCongr (rfl : k = k)).hom = 𝟙 (pushforward k) := by
    ext M U
    simp
  rw [he]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_equality_app {X Y : Scheme.{u}} (k l : X ⟶ Y)
    (e : k = l) (A : Y.Modules) :
    (eqToHom (congrArg tensorPullback e)).app A =
      (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj A) e)).hom := by
  subst l
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse conjugate of a pushforward square is the tensor pullback square.
Source: Stacks Project, Tags 0095, 0096 and 0097 (tensor formula, adjunction,
and composition), and
08HY (the pushforward square used to define base change).
(blueprint: lem-sc-picard-tensor-square-conjugacy)

Proof: Transport each tensor pullback to ordinary pullback by
`picardTensorComparison`. The conjugate of each comparison is the identity,
by uniqueness of left adjoints. Whiskering these identities and using
`conjugateEquiv_comp` reduces each composition comparison to
`conjugateEquiv_pullbackComp_inv`. For the middle equality comparison,
substitute equal morphisms; its conjugate is the identity and equals the
pushforward equality comparison, as checked on sections. Therefore the
conjugate of the three-factor pullback square is the three-factor pushforward
square. Apply inverse conjugation and evaluate at A. The component of the
bundled tensor composition isomorphism is definitionally `picardTensorCompIso`.
Substituting equal morphisms identifies the component of functor equality
transport with object equality transport. No cartesian assumption or invertibility
of the base-change map is used, and the calculation applies to zero modules and
empty schemes. -/
theorem picardTensorSquareConjugacy
    {X S T X' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    (g : T ⟶ S) (v : X' ⟶ X) (e : v ≫ f = f' ≫ g) (A : S.Modules) :
    let adj : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), tensorPullback k ⊣ pushforward k :=
      fun k ↦ Classical.choose (exists_tensorPullbackAdjunction k)
    ((conjugateEquiv ((adj f).comp (adj v)) ((adj g).comp (adj f'))).symm
      ((pushforwardComp v f).hom ≫ (pushforwardCongr e).hom ≫
        (pushforwardComp f' g).inv)).app A =
    (picardTensorCompIso f' g A ≪≫
      eqToIso (congrArg (fun k ↦ (tensorPullback k).obj A) e.symm) ≪≫
      (picardTensorCompIso v f A).symm).hom := by
  dsimp only
  rw [← conjugateEquiv_symm_comp _
    (Classical.choose (exists_tensorPullbackAdjunction (v ≫ f)))]
  rw [← conjugateEquiv_symm_comp _
    (Classical.choose (exists_tensorPullbackAdjunction (f' ≫ g)))]
  rw [tensorComp_hom_mate, tensorComp_inv_mate, equality_mate]
  simp only [NatTrans.comp_app]
  rw [tensor_equality_app (f' ≫ g) (v ≫ f) e.symm A]
  simp only [← Iso.app_hom, ← Iso.app_inv, tensorComp_app f' g A,
    tensorComp_app v f A, Iso.trans_hom, Iso.symm_hom, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
