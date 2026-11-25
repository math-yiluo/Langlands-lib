/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorCoefficientComparison

/-! # Ordinary pullback composition of the fixed tensor coefficient comparisons

Source: Stacks Project, Tags 0096 and 0D5S;
Mathlib `Adjunction.leftAdjointCompIso_assoc`.
(blueprint: lem-sc-tensor-coefficient-pullback-composition).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

-- Converting the second left adjoint does not change the right-adjoint mate.
private theorem mixed
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {T P : B ⥤ C} {H : A ⥤ C}
    {R : B ⥤ A} {S : C ⥤ B} {U : C ⥤ A}
    (a : F ⊣ R) (b : T ⊣ S) (b' : P ⊣ S) (c : H ⊣ U)
    (e : S ⋙ R ≅ U) :
    Functor.whiskerLeft F (b.leftAdjointUniq b').inv ≫
      ((conjugateIsoEquiv (a.comp b) c).symm e).inv =
      (Adjunction.leftAdjointCompIso a b' c e).hom := by
  apply (conjugateEquiv c (a.comp b')).injective
  rw [← conjugateEquiv_comp c (a.comp b) (a.comp b')]
  rw [conjugateEquiv_whiskerLeft]
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointCompIso,
    conjugateIsoEquiv_symm_apply_inv, conjugateIsoEquiv_symm_apply_hom]

private theorem coefficient_hom_comp {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    (tensorCoefficientComparison q q1 a h L).hom =
      (Adjunction.leftAdjointCompIso (coefficientTensorAdjunction q)
        (pullbackPushforwardAdjunction a) (coefficientTensorAdjunction q1)
        (pushforwardComp a q ≪≫ pushforwardCongr h)).hom.app L := by
  simpa only [tensorCoefficientComparison, coefficientOrdinaryPullbackComparison,
    coefficientTensorTriangle, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app] using
    congrArg (fun t ↦ t.app L) (mixed (coefficientTensorAdjunction q)
      (coefficientTensorAdjunction a) (pullbackPushforwardAdjunction a)
      (coefficientTensorAdjunction q1) (pushforwardComp a q ≪≫ pushforwardCongr h))

/-- The ordinary coefficient comparisons respect a commuting triangle of pullbacks.
Source: Stacks Project, Tags 0096 and 0D5S; step 2 of
`lem-sc-tensor-single-pullback-composition`.
(blueprint: lem-sc-tensor-coefficient-pullback-composition)

Proof: Substitute a' = b ≫ a. Conjugation sends the ordinary-to-tensor
uniqueness comparison to the identity, so each coefficient comparison is the
component of the mixed leftAdjointCompIso for tensor pullback along q and
ordinary pullback along a, with right-adjoint comparison pushforwardComp a q
followed by pushforwardCongr h1. The same identification applies to b and b ≫ a.
The ordinary pullbackComp b a is also leftAdjointCompIso, as follows by
injectivity of conjugateEquiv and conjugateEquiv_pullbackComp_inv. Apply Mathlib's
Adjunction.leftAdjointCompIso_assoc to these six adjunctions. Its right-adjoint
coherence hypothesis is checked after substituting q1 and q2: at every module
and open, pushforward composition is the identity and equality transport is the
presheaf map of equality of opens. Functoriality and proof irrelevance identify
the paths. Evaluate the resulting natural-isomorphism equality at L. Zero
modules, identity morphisms and empty schemes require no additional hypotheses;
no derived category or flatness assumption occurs. -/
theorem tensorCoefficientPullback_composition
    {A B C X : Scheme.{v}} (q : A ⟶ X) (q1 : B ⟶ X) (q2 : C ⟶ X)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (h1 : a ≫ q = q1) (h2 : b ≫ q1 = q2) (h3 : a' ≫ q = q2)
    (hab : b ≫ a = a') (L : X.Modules) :
    (pullback b).map (tensorCoefficientComparison q q1 a h1 L).hom ≫
      (tensorCoefficientComparison q1 q2 b h2 L).hom =
    (pullbackComp b a ≪≫ eqToIso (congrArg (fun r ↦ pullback r) hab)).hom.app
      ((tensorPullback q).obj L) ≫ (tensorCoefficientComparison q q2 a' h3 L).hom := by
  subst a'
  have hp : Adjunction.leftAdjointCompIso (pullbackPushforwardAdjunction a)
      (pullbackPushforwardAdjunction b) (pullbackPushforwardAdjunction (b ≫ a))
      (pushforwardComp b a) = pullbackComp b a := by
    apply Iso.ext_inv
    apply (conjugateEquiv ((pullbackPushforwardAdjunction a).comp
      (pullbackPushforwardAdjunction b)) (pullbackPushforwardAdjunction (b ≫ a))).injective
    simp only [Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      conjugateEquiv_pullbackComp_inv]
  have hi := Adjunction.leftAdjointCompIso_assoc (coefficientTensorAdjunction q)
    (pullbackPushforwardAdjunction a) (pullbackPushforwardAdjunction b)
    (coefficientTensorAdjunction q1) (pullbackPushforwardAdjunction (b ≫ a))
    (coefficientTensorAdjunction q2)
    (pushforwardComp a q ≪≫ pushforwardCongr h1) (pushforwardComp b a)
    (pushforwardComp (b ≫ a) q ≪≫ pushforwardCongr h3)
    (pushforwardComp b q1 ≪≫ pushforwardCongr h2) (by
      subst q1
      subst q2
      ext M U
      simp)
  have hh := congrArg (fun e ↦ e.hom.app L) hi
  simpa only [coefficient_hom_comp, hp, eqToIso_refl, Iso.trans_refl,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] using hh.symm

end
end AlgebraicGeometry.Scheme.Modules
