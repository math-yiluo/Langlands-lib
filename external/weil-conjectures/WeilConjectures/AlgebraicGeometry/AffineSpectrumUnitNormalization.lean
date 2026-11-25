/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates

/-! # Affine spectrum unit normalization

Source: Stacks Project, Tag 0D5S, composition coherence used in the affine reduction.
(blueprint: lem-pc-affine-spectrum-unit-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

-- Work through the constructed pullback functor interface during coherence calculations.

/-- The triangle equation for composition units follows from associativity and the
left and right unit laws. Transport the two composites of the spectrum isomorphism
and its inverse to identities, apply those unit laws, and identify the remaining
transport maps by proof irrelevance. This is the coherence part of the normalization
proof below. Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-affine-spectrum-unit-normalization). -/
private theorem composition_unit_triangle
    (F : ∀ {P Q : Scheme.{u}}, (P ⟶ Q) →
      (schemeDerivedCategory Q ⥤ schemeDerivedCategory P))
    (c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      F l ⋙ F k ≅ F (k ≫ l))
    (i : ∀ Y : Scheme.{u}, F (𝟙 Y) ≅ 𝟭 _)
    (huL : ∀ {P Q : Scheme.{u}} (f : P ⟶ Q),
      c (𝟙 P) f ≪≫
        eqToIso (congrArg (fun k : P ⟶ Q ↦ F k) (Category.id_comp f)) =
      Functor.isoWhiskerLeft (F f) (i P) ≪≫
        Functor.rightUnitor (F f))
    (huR : ∀ {P Q : Scheme.{u}} (f : P ⟶ Q),
      c f (𝟙 Q) ≪≫
        eqToIso (congrArg (fun k : P ⟶ Q ↦ F k) (Category.comp_id f)) =
      Functor.isoWhiskerRight (i Q) (F f) ≪≫
        Functor.leftUnitor (F f))
    (hassoc : ∀ {W P Q Z : Scheme.{u}} (h : W ⟶ P) (f : P ⟶ Q) (g : Q ⟶ Z),
      Functor.isoWhiskerRight (c f g) (F h) ≪≫ c h (f ≫ g) =
      Functor.associator (F g) (F f) (F h) ≪≫
        Functor.isoWhiskerLeft (F g) (c h f) ≪≫ c (h ≫ f) g ≪≫
        eqToIso (congrArg (fun k : W ⟶ Z ↦ F k) (Category.assoc h f g)))
    (X : Scheme.{u}) [IsAffine X] (K : schemeDerivedCategory X) :
  let a := c X.isoSpec.hom X.isoSpec.inv ≪≫
    eqToIso (congrArg (fun k : X ⟶ X ↦ F k) X.isoSpec.hom_inv_id) ≪≫ i X
  let b := c X.isoSpec.inv X.isoSpec.hom ≪≫
    eqToIso (congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) ↦ F k)
      X.isoSpec.inv_hom_id) ≪≫ i (Spec Γ(X, ⊤))
  (F X.isoSpec.inv).map (a.hom.app K) =
    b.hom.app ((F X.isoSpec.inv).obj K) := by
  let a := c X.isoSpec.hom X.isoSpec.inv ≪≫
    eqToIso (congrArg (fun k : X ⟶ X ↦ F k) X.isoSpec.hom_inv_id) ≪≫ i X
  let b := c X.isoSpec.inv X.isoSpec.hom ≪≫
    eqToIso (congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) ↦ F k)
      X.isoSpec.inv_hom_id) ≪≫ i (Spec Γ(X, ⊤))
  have rightUnit {P Q : Scheme.{u}} (v : P ⟶ Q) (l : Q ⟶ Q)
      (hl : l = 𝟙 Q) (K : schemeDerivedCategory Q) :
      (F v).map
          ((eqToIso (congrArg (fun k : Q ⟶ Q ↦ F k) hl) ≪≫ i Q).hom.app K) =
        (c v l).hom.app K ≫
          (eqToIso (congrArg (fun k : P ⟶ Q ↦ F k)
            ((congrArg (fun k ↦ v ≫ k) hl).trans (Category.comp_id v)))).hom.app K := by
    subst l
    simpa only [eqToIso_refl, Iso.refl_trans, Functor.isoWhiskerRight_hom,
      Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_obj, Functor.id_obj, Category.comp_id] using
      (congrArg (fun t ↦ t.hom.app K) (huR v)).symm
  have leftUnit {P Q : Scheme.{u}} (l : P ⟶ P) (v : P ⟶ Q)
      (hl : l = 𝟙 P) (K : schemeDerivedCategory Q) :
      (eqToIso (congrArg (fun k : P ⟶ P ↦ F k) hl) ≪≫ i P).hom.app
          ((F v).obj K) =
        (c l v).hom.app K ≫
          (eqToIso (congrArg (fun k : P ⟶ Q ↦ F k)
            ((congrArg (fun k ↦ k ≫ v) hl).trans (Category.id_comp v)))).hom.app K := by
    subst l
    simpa only [eqToIso_refl, Iso.refl_trans, Functor.isoWhiskerLeft_hom,
      Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_obj, Functor.id_obj, Category.comp_id] using
      (congrArg (fun t ↦ t.hom.app K) (huL v)).symm
  have ha := congrArg (fun t ↦ t.hom.app K)
    (hassoc X.isoSpec.inv X.isoSpec.hom X.isoSpec.inv)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  dsimp only [a, b]
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    rightUnit X.isoSpec.inv _ X.isoSpec.hom_inv_id]
  rw [← Category.assoc, ha, Category.assoc]
  rw [Iso.trans_hom, NatTrans.comp_app,
    leftUnit _ X.isoSpec.inv X.isoSpec.inv_hom_id]
  simp only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans]

/-- The inverse unit of the adjointified spectrum equivalence is the original
composition comparison followed by the identity comparison.

Proof: write h = isoSpec.hom and v = isoSpec.inv, and let a and b be the
composition/identity comparisons for h;v and v;h respectively. Apply the
associativity law for c to v,h,v. Transport h;v and v;h along the two inverse
identities. The right unit law at v identifies c(v,id) with pullback of i X;
the left unit law at v identifies c(id,v) with i(Spec Γ(X,⊤)) at v* K.
After cancelling the common composition comparison, the resulting equation
is v*.map(a.app K) = b.app(v*.obj K). Invert this equation to obtain the
triangle law for a.symm and b. The equivalence constructed by Equivalence.mk
has the same counit b and a faithful forward functor v*. Its inverse unit
also maps to b at v*.obj K, by Equivalence.counit_app_functor. Faithfulness
therefore identifies its inverse unit with a, component by component.
Source: Stacks Project, Tag 0D5S, composition of derived pullbacks; the triangle
calculation is the first step of the original cancellation node's proof.
(blueprint: lem-pc-affine-spectrum-unit-normalization). -/
theorem affineSpectrum_unit_normalization (X : Scheme.{u}) [IsAffine X] :
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  (affineSpectrumInversePullbackEquivalence X).unitIso.inv =
    (c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫
      i X).hom := by
  classical
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  let a := c X.isoSpec.hom X.isoSpec.inv ≪≫
    eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫ i X
  let b := c X.isoSpec.inv X.isoSpec.hom ≪≫
    eqToIso (congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) ↦ derivedPullback k)
      X.isoSpec.inv_hom_id) ≪≫ i (Spec Γ(X, ⊤))
  have laws := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  have triangle :=
    composition_unit_triangle (fun f ↦ derivedPullback f) c i laws.1 laws.2.1 laws.2.2 X
  let e := affineSpectrumInversePullbackEquivalence X
  change e.unitIso.inv = a.hom
  apply NatTrans.ext
  funext K
  apply e.functor.map_injective
  exact (e.counit_app_functor K).symm.trans (triangle K).symm

end AlgebraicGeometry
