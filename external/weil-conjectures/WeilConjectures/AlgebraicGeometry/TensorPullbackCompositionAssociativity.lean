/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Associativity of the canonical tensor pullback comparisons
Source: Stacks Project, Sheaves of Modules, Tags 0095 and 0096.
(blueprint: lem-pc-tensor-pullback-composition-associativity). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] tensorPullback

/-- The two routes from a triple composite to its three tensor pullbacks agree.
Source: Stacks Project, Tags 0095 and 0096, composition of module pullbacks.
(blueprint: lem-pc-tensor-pullback-composition-associativity).
Proof: Substitute the four factorization equalities. Apply the conjugate
natural-transformation equivalence for the adjunction of the total pullback
and the composite of the three chosen tensor pullback adjunctions. Conjugation
preserves composition, whiskering and associators (Mathlib's conjugateEquiv_comp,
conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight and
conjugateEquiv_associator_hom). The two sides become the two composites of
pushforward composition comparisons. These agree: on every open set their
components are identity maps of sections, with the equality transports
identified by proof irrelevance. Injectivity of conjugation proves equality of
natural transformations. Evaluate at M; functor associators evaluate to the
identity, giving exactly the three factors on each side below. No assumption
on M or the morphisms is required; identities and the zero module are included. -/
theorem tensorPullbackCompositionIso_associativity
    {X₀ X₁ X₂ Z : Scheme.{u}}
    (h : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (p : Z ⟶ X₂)
    (b : Z ⟶ X₁) (a : Z ⟶ X₀) (d : X₂ ⟶ X₀)
    (wpq : p ≫ q = b) (wqh : q ≫ h = d)
    (wbh : b ≫ h = a) (wpd : p ≫ d = a) (M : X₀.Modules) :
    (tensorPullbackCompositionIso p d a wpd).hom.app M ≫
        (tensorPullback p).map ((tensorPullbackCompositionIso q h d wqh).hom.app M) =
      (tensorPullbackCompositionIso b h a wbh).hom.app M ≫
        (tensorPullbackCompositionIso p q b wpq).hom.app ((tensorPullback h).obj M) :=
  by
    let ah := Classical.choose (exists_tensorPullbackAdjunction h)
    let aq := Classical.choose (exists_tensorPullbackAdjunction q)
    let ap := Classical.choose (exists_tensorPullbackAdjunction p)
    let ad := Classical.choose (exists_tensorPullbackAdjunction d)
    let ab := Classical.choose (exists_tensorPullbackAdjunction b)
    let aa := Classical.choose (exists_tensorPullbackAdjunction a)
    let ehd := pushforwardComp q h ≪≫ pushforwardCongr wqh
    let eqb := pushforwardComp p q ≪≫ pushforwardCongr wpq
    let eha := pushforwardComp b h ≪≫ pushforwardCongr wbh
    let eda := pushforwardComp p d ≪≫ pushforwardCongr wpd
    have hc : Functor.isoWhiskerLeft (pushforward p) ehd ≪≫ eda =
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight eqb (pushforward h) ≪≫ eha := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      apply hom_ext
      intro U
      simp only [ehd, eqb, eha, eda, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
        Functor.associator_inv_app, Hom.comp_app, pushforward_map_app,
        pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
        Category.id_comp, pushforward_obj_presheaf_map]
      change (N.presheaf.map _ ≫ N.presheaf.map _) =
        (N.presheaf.map _ ≫ N.presheaf.map _)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    have ht := Adjunction.leftAdjointCompIso_assoc ah aq ap ad ab aa ehd eqb eha eda hc
    have eqComp {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
        (k : Z ⟶ X) (w : f ≫ g = k) :
        (Adjunction.leftAdjointCompIso
          (Classical.choose (exists_tensorPullbackAdjunction g))
          (Classical.choose (exists_tensorPullbackAdjunction f))
          (Classical.choose (exists_tensorPullbackAdjunction k))
          (pushforwardComp f g ≪≫ pushforwardCongr w)).inv =
        (tensorPullbackCompositionIso f g k w).hom := by
      simp only [Adjunction.leftAdjointCompIso, tensorPullbackCompositionIso]
      rfl
    have hi := congrArg (fun i ↦ i.inv.app M) ht
    dsimp only [ah, aq, ap, ad, ab, aa, ehd, eqb, eha, eda] at hi
    simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_inv, Functor.associator_hom_app, Category.comp_id, eqComp] using hi.symm


end AlgebraicGeometry.Scheme.Modules
