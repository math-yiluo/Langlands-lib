/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescent

/-! # Equality of projection pullbacks after restriction to the closed fibre

Source: Stacks Project, Tag 09ZF, proof of lemma-gabber-h0, third paragraph
and fourth paragraph's parenthetical comparison on Z' times_Z Z'
(blueprint: lem-weil-pbc-gabber-h0-projection-restrictions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry



set_option backward.defeqAttrib.useBackward true in
private theorem cancel_cast_comp {V : Scheme.{u}} {A B T : V.Etale}
    (e : A = B) (e' : B = A) (m : B ⟶ T) (n : A ⟶ T)
    (hm : m = eqToHom e' ≫ n) : eqToHom e ≫ m = n := by
  subst B
  simpa using hm

set_option backward.defeqAttrib.useBackward true in
private theorem map_transport {X V : Scheme.{u}} {f g : V ⟶ X} (e : f = g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) (A : V.Etale)
    (v : (MorphismProperty.Over.pullback @Etale ⊤ f).obj U ⟶ A) (v' :
      (MorphismProperty.Over.pullback @Etale ⊤ g).obj U ⟶ A)
    (hv : eqToHom (congrArg (fun k : V ⟶ X ↦ (MorphismProperty.Over.pullback @Etale ⊤ k).obj U) e) ≫
      v' = v)
    (s : ((Scheme.etaleSetPullback f).obj F).obj.obj (op A)) :
    HEq (((Scheme.etaleSetPullback g).obj F).obj.map v'.op
      ((eqToHom (congrArg (fun k : V ⟶ X ↦ (Scheme.etaleSetPullback k).obj F) e)).hom.app (op A) s))
      (((Scheme.etaleSetPullback f).obj F).obj.map v.op s) := by
  subst g
  simp only [eqToHom_refl, Category.id_comp] at hv
  subst v'
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem pasting_transport {X Y W : Scheme.{u}}
    (f : W ⟶ Y) (g : Y ⟶ X) (k : W ⟶ X) (hk : k = f ≫ g) (U : X.Etale) :
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g k hk).hom.app U =
      eqToHom (congrArg (fun k : W ⟶ X ↦ (MorphismProperty.Over.pullback @Etale ⊤ k).obj U) hk) ≫
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).hom.app U := by
  subst k
  simp

/-- The associativity comparison on an over category, evaluated at one object. -/
private theorem pullbackComp_assoc_hom {C : Type*} [Category C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {X Y W V : C} (f : Y ⟶ X) (g : W ⟶ Y) (j : V ⟶ W) (U : P.Over ⊤ X) :
    eqToHom (congrArg (fun k : V ⟶ X ↦ (MorphismProperty.Over.pullback P ⊤ k).obj U)
        (Category.assoc j g f)) ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) j (g ≫ f)).hom.app U ≫
        (MorphismProperty.Over.pullback P ⊤ j).map
          ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) g f).hom.app U) =
      (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) (j ≫ g) f).hom.app U ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) j g).hom.app
          ((MorphismProperty.Over.pullback P ⊤ f).obj U) := by
  have transport (k : V ⟶ X) (hk : k = (j ≫ g) ≫ f) :
      (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) (j ≫ g) f k hk).hom.app U =
        eqToHom (congrArg (fun k : V ⟶ X ↦ (MorphismProperty.Over.pullback P ⊤ k).obj U)
          hk) ≫ (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) (j ≫ g) f).hom.app U := by
    subst k
    simp
  have hp := congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := ⊤) j g f)) U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hp
  rw [transport (j ≫ g ≫ f) (Category.assoc j g f).symm, Category.assoc] at hp
  rw [hp, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
private theorem comparison_assoc {X Y W V : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y) (j : V ⟶ W)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U))) :
    HEq (etaleSetDescentComparison (g ≫ f) j F U (etaleSetDescentComparison f g F U s))
      (etaleSetDescentComparison f (j ≫ g) F U s) := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let pc := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f
  let w := etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F)
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) s
  have hn₁ := etaleSetInverseImageCompositionUnits.1 W V j
    ((Scheme.etaleSetPullback (g ≫ f)).obj F) ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ((MorphismProperty.Over.pullback @Etale ⊤
      (g ≫ f)).obj U)
    (pc.hom.app U) (((c X Y W f g).hom.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj ((MorphismProperty.Over.pullback @Etale ⊤
        f).obj U))) w)
  have hn₂ := etaleSetInverseImageCompositionUnits.2.1 W V j
    ((Scheme.etaleSetPullback g).obj ((Scheme.etaleSetPullback f).obj F)) ((Scheme.etaleSetPullback
      (g ≫ f)).obj F)
    ((c X Y W f g).hom.app F) ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) w
  have hc := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
    X Y W V f g j F
  have hu := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
    Y W V g j ((Scheme.etaleSetPullback f).obj F) ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
      U) s
  have hn₃ := ConcreteCategory.congr_hom
    (((c X W V (g ≫ f) j).hom.app F).hom.naturality
      (((MorphismProperty.Over.pullback @Etale ⊤ j).map (pc.hom.app U)).op))
    (etaleSetDescentUnit j ((Scheme.etaleSetPullback (g ≫ f)).obj F)
      ((MorphismProperty.Over.pullback @Etale ⊤ g).obj ((MorphismProperty.Over.pullback @Etale ⊤
        f).obj U))
      (((c X Y W f g).hom.app F).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) w))
  have hn₄ := ConcreteCategory.congr_hom
    (((c X Y V f (j ≫ g)).hom.app F).hom.naturality
      (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j g).inv.app
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)).op))
    (etaleSetDescentUnit (j ≫ g) ((Scheme.etaleSetPullback f).obj F)
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) s)
  unfold etaleSetDescentComparison
  erw [hn₁]
  simp only [ConcreteCategory.comp_apply] at hn₃
  erw [hn₃]
  erw [hn₂]
  let v := etaleSetDescentUnit j ((Scheme.etaleSetPullback g).obj ((Scheme.etaleSetPullback f).obj
    F))
    ((MorphismProperty.Over.pullback @Etale ⊤ g).obj ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U)) w
  have hc' := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun k ↦ k.hom) hc) (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ g).obj ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U))))) v
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hc'
  erw [hc']
  have hv := pullbackComp_assoc_hom (@Etale) f g j U
  refine (heq_of_eq
    (((Scheme.etaleSetPullback (j ≫ g ≫ f)).obj F).obj.map_comp_apply
      (((MorphismProperty.Over.pullback @Etale ⊤ j).map (pc.hom.app U)).op)
      (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j (g ≫ f)).hom.app U).op)
      _).symm).trans ?_
  refine (map_transport (Category.assoc j g f) F U
    ((MorphismProperty.Over.pullback @Etale ⊤ j).obj ((MorphismProperty.Over.pullback @Etale ⊤
      g).obj ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) _ _ hv _).trans ?_
  simp only [ConcreteCategory.comp_apply] at hn₄
  erw [hu]
  erw [hn₄]
  erw [← ((Scheme.etaleSetPullback ((j ≫ g) ≫ f)).obj F).obj.map_comp_apply, ← op_comp]
  erw [@Category.assoc V.Etale inferInstance, Iso.hom_inv_id_app, Category.comp_id]
  rfl


set_option backward.defeqAttrib.useBackward true in
private theorem comparison_heq {X Y W : Scheme.{u}}
    {f f' : Y ⟶ X} {g g' : W ⟶ Y} (hf : f = f') (hg : g = g')
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U)))
    (s' : ((Scheme.etaleSetPullback f').obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f').obj U))) (hs : HEq s s') :
    HEq (etaleSetDescentComparison f g F U s) (etaleSetDescentComparison f' g' F U s') := by
  subst f'
  subst g'
  exact heq_of_eq (congrArg (etaleSetDescentComparison f g F U) (eq_of_heq hs))

set_option backward.defeqAttrib.useBackward true in
private theorem transport_heq {α β : Type (u + 1)} (e : α = β) (s : α) :
    HEq (eqToHom e s) s := by
  subst β
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem comparison_cast {X Y W : Scheme.{u}}
    {f f' : Y ⟶ X} (hf : f = f') (g : W ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U))) :
    HEq (etaleSetDescentComparison f g F U s)
      (etaleSetDescentComparison f' g F U (eqToHom (congrArg
        (fun k : Y ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj (op
          ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) hf) s)) := by
  subst f'
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem comparison_cancel {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s t : ((Scheme.etaleSetPullback f).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U)))
    (hs : etaleSetDescentComparison f g F U s = etaleSetDescentComparison f g F U t) :
    etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F) ((MorphismProperty.Over.pullback
      @Etale ⊤ f).obj U) s =
      etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F) ((MorphismProperty.Over.pullback
        @Etale ⊤ f).obj U) t := by
  unfold etaleSetDescentComparison at hs
  have hi := ConcreteCategory.bijective_of_isIso
    (((Scheme.etaleSetPullback (g ≫ f)).obj F).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app U).op)
  apply (ConcreteCategory.bijective_of_isIso
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2) X Y W f g).hom.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj ((MorphismProperty.Over.pullback @Etale ⊤
        f).obj U))))).injective
  exact hi.injective hs

set_option backward.defeqAttrib.useBackward true in
private theorem comparison_square {X A B V D : Scheme.{u}}
    (f : A ⟶ X) (h : B ⟶ X) (r : V ⟶ A) (k : V ⟶ B)
    (e : r ≫ f = k ≫ h)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (t : ((Scheme.etaleSetPullback f).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U)))
    (s : ((Scheme.etaleSetPullback h).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      h).obj U)))
    (hc : HEq (etaleSetDescentComparison f r F U t) (etaleSetDescentComparison h k F U s)) (q : D ⟶
      V) :
    HEq (etaleSetDescentComparison f (q ≫ r) F U t) (etaleSetDescentComparison h (q ≫ k) F U s) :=
      by
  exact (comparison_assoc f r q F U t).symm.trans
    ((comparison_heq e rfl F U _ _ hc).trans (comparison_assoc h k q F U s))

set_option backward.defeqAttrib.useBackward true in
private theorem restricted_comparisons {X B Y D : Scheme.{u}}
    (h : B ⟶ X) (p₁ p₂ : Y ⟶ B) (hp : p₂ ≫ h = p₁ ≫ h) (j : D ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback h).obj F).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      h).obj U)))
    (he : HEq (etaleSetDescentComparison h (j ≫ p₁) F U s) (etaleSetDescentComparison h (j ≫ p₂) F U
      s)) :
    etaleSetDescentUnit j ((Scheme.etaleSetPullback (p₁ ≫ h)).obj F)
      ((MorphismProperty.Over.pullback @Etale ⊤ (p₁ ≫ h)).obj U)
        (etaleSetDescentComparison h p₁ F U s) =
      etaleSetDescentUnit j ((Scheme.etaleSetPullback (p₁ ≫ h)).obj F)
        ((MorphismProperty.Over.pullback @Etale ⊤ (p₁ ≫ h)).obj U)
        (eqToHom (congrArg
          (fun k : Y ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj (op
            ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) hp)
          (etaleSetDescentComparison h p₂ F U s)) := by
  apply comparison_cancel (p₁ ≫ h) j F U
  apply eq_of_heq
  exact (comparison_assoc h p₁ j F U s).trans
    (he.trans ((comparison_assoc h p₂ j F U s).symm.trans
      (comparison_cast hp j F U _)))

set_option backward.defeqAttrib.useBackward true in
/-- A compatible section has equal projection pullbacks after restriction.
Source: Stacks Project, Tag 09ZF, proof of lemma-gabber-h0, third paragraph
and fourth paragraph: "this is true for the pullbacks of t'"
(blueprint: lem-weil-pbc-gabber-h0-projection-restrictions).

Proof:
Put Y = X' times_X X', a = p_1 followed by h = p_2 followed by h,
and D = Z times_X Y with j : D to Y. Put Z' = Z times_X X' and k : Z' to X'.
For each projection p_r : Y to X', the pullback property gives q_r : D to Z'
with q_r followed by k = j followed by p_r and q_r followed by (Z' to Z)
equal to the projection D to Z. Apply the unit along q_r to hres. Naturality
in the sheaf and the unit-compatible composition isomorphisms identify its
right side with the restriction along j of the p_r-pullback of s', transported
to a^*F. More explicitly, after comparison to the composite inverse image,
this section equals c_(h,p_r j)((p_r j)^*s') = c_(h,k q_r)((k q_r)^*s').
Composition associativity rewrites it as the pullback along q_r of
c_(h,k)(k^*s'). By hres this is the pullback along q_r of
c_(i,Z' to Z)((Z' to Z)^*t), hence equals c_(i,D to Z)((D to Z)^*t).
This is independent of r. The fibre-product pasting maps agree because their
projections agree. The composition comparison is an isomorphism, so cancel
it to obtain equality under the raw unit along j, as stated. The transport
for p_2 is exactly eqToHom along pullback.condition.symm; all other transports
come from the same projection equalities. No closed-immersion, finiteness,
surjectivity, or injectivity assumption is used. Identity and empty schemes
are allowed: this calculation only uses the pullback universal property. -/
theorem gabber_h0_projection_restrictions
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s' : ((Scheme.etaleSetPullback h).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X)))))
    (hres : etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t =
        eqToHom (congrArg
          (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X)) s')) :
    let a : pullback h h ⟶ X := pullback.fst h h ≫ h
    let j : pullback i a ⟶ pullback h h := pullback.snd i a
    let G := (Scheme.etaleSetPullback a).obj F
    let U := (MorphismProperty.Over.pullback @Etale ⊤ a).obj (Scheme.Etale.mk (𝟙 X))
    etaleSetDescentUnit j G U
      (etaleSetDescentComparison h (pullback.fst h h) F (Scheme.Etale.mk (𝟙 X)) s') =
    etaleSetDescentUnit j G U
      (eqToHom (congrArg
          (fun k : pullback h h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := h) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd h h) F (Scheme.Etale.mk (𝟙 X)) s')) := by
  dsimp only
  let Y := pullback h h
  let a : Y ⟶ X := pullback.fst h h ≫ h
  let D := pullback i a
  let j : D ⟶ Y := pullback.snd i a
  let z : D ⟶ Z := pullback.fst i a
  let r : pullback i h ⟶ Z := pullback.fst i h
  let k : pullback i h ⟶ X' := pullback.snd i h
  let p₁ : Y ⟶ X' := pullback.fst h h
  let p₂ : Y ⟶ X' := pullback.snd h h
  have hp : p₂ ≫ h = a := (pullback.condition (f := h) (g := h)).symm
  have hz : z ≫ i = j ≫ a := pullback.condition
  have hq₁ : z ≫ i = (j ≫ p₁) ≫ h := by
    simpa [a, p₁, Category.assoc] using hz
  have hq₂ : z ≫ i = (j ≫ p₂) ≫ h := by
    rw [Category.assoc, hp]
    exact hz
  let q₁ : D ⟶ pullback i h := pullback.lift z (j ≫ p₁) hq₁
  let q₂ : D ⟶ pullback i h := pullback.lift z (j ≫ p₂) hq₂
  have hr₁ : q₁ ≫ r = z := pullback.lift_fst _ _ _
  have hr₂ : q₂ ≫ r = z := pullback.lift_fst _ _ _
  have hk₁ : q₁ ≫ k = j ≫ p₁ := pullback.lift_snd _ _ _
  have hk₂ : q₂ ≫ k = j ≫ p₂ := pullback.lift_snd _ _ _
  have hc : HEq (etaleSetDescentComparison i r F (Scheme.Etale.mk (𝟙 X)) t)
      (etaleSetDescentComparison h k F (Scheme.Etale.mk (𝟙 X)) s') :=
    (heq_of_eq hres).trans (transport_heq _ _)
  have square (q : D ⟶ pullback i h) :
      HEq (etaleSetDescentComparison i (q ≫ r) F (Scheme.Etale.mk (𝟙 X)) t)
        (etaleSetDescentComparison h (q ≫ k) F (Scheme.Etale.mk (𝟙 X)) s') := by
    exact comparison_square i h r k pullback.condition F _ t s' hc q
  have he : HEq (etaleSetDescentComparison h (j ≫ p₁) F (Scheme.Etale.mk (𝟙 X)) s')
      (etaleSetDescentComparison h (j ≫ p₂) F (Scheme.Etale.mk (𝟙 X)) s') := by
    have H₁ := square q₁
    have H₂ := square q₂
    rw [hr₁, hk₁] at H₁
    rw [hr₂, hk₂] at H₂
    exact H₁.symm.trans H₂
  exact restricted_comparisons h p₁ p₂ hp j F (Scheme.Etale.mk (𝟙 X)) s' he

end AlgebraicGeometry
