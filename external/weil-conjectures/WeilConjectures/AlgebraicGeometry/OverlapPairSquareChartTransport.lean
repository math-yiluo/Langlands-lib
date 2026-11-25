/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-! # Transport of pair squares through chart refinements

Source: Stacks Project, Tag 01ZR, first proof; Mathlib pullHom composition.
(blueprint: lem-pc-overlap-pair-square-chart-transport). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor

set_option backward.isDefEq.respectTransparency false in
private lemma pair_square_iff
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {S T X₁ X₂ X₁' X₂' : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p : T ⟶ S) (v₁ : X₁' ⟶ X₁) (v₂ : X₂' ⟶ X₂)
    (g₁ : X₁' ⟶ T) (g₂ : X₂' ⟶ T)
    (w₁ : v₁ ≫ f₁ = g₁ ≫ p) (w₂ : v₂ ≫ f₂ = g₂ ≫ p)
    (A₁ : F.obj (.mk (op X₁))) (A₂ : F.obj (.mk (op X₂)))
    (M : F.obj (.mk (op T)))
    (e₁ : (F.map v₁.op.toLoc).toFunctor.obj A₁ ≅ (F.map g₁.op.toLoc).toFunctor.obj M)
    (e₂ : (F.map v₂.op.toLoc).toFunctor.obj A₂ ≅ (F.map g₂.op.toLoc).toFunctor.obj M)
    (φ : (F.map (pullback.fst f₁ f₂).op.toLoc).toFunctor.obj A₁ ⟶
      (F.map (pullback.snd f₁ f₂).op.toLoc).toFunctor.obj A₂) :
    let s₁ := pullback.fst g₁ g₂
    let s₂ := pullback.snd g₁ g₂
    let q := s₁ ≫ g₁
    let k := pullback.lift (s₁ ≫ v₁) (s₂ ≫ v₂) (by
      rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc,
        ← Category.assoc, pullback.condition])
    (F.map s₁.op.toLoc).toFunctor.map e₁.hom ≫
        (F.mapComp' g₁.op.toLoc s₁.op.toLoc q.op.toLoc).inv.toNatTrans.app M ≫
        (F.mapComp' g₂.op.toLoc s₂.op.toLoc q.op.toLoc
          (by dsimp [q, s₁, s₂]
              simp only [← Quiver.Hom.comp_toLoc, ← op_comp,
                pullback.condition])).hom.toNatTrans.app M =
      F.overlapPairBaseChangeHom f₁ f₂ p v₁ v₂ g₁ g₂ w₁ w₂ A₁ A₂ φ ≫
        (F.map s₂.op.toLoc).toFunctor.map e₂.hom ↔
    pullHom e₁.hom s₁ (s₁ ≫ v₁) q rfl rfl =
      pullHom φ k (s₁ ≫ v₁) (s₂ ≫ v₂)
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ≫
      pullHom e₂.hom s₂ (s₂ ≫ v₂) q rfl pullback.condition.symm := by
  dsimp only
  rw [← cancel_epi
    ((F.mapComp v₁.op.toLoc (pullback.fst g₁ g₂).op.toLoc).hom.toNatTrans.app A₁),
    ← cancel_mono
    ((F.mapComp' g₂.op.toLoc (pullback.snd g₁ g₂).op.toLoc
      (pullback.fst g₁ g₂ ≫ g₁).op.toLoc
      (by simp only [← Quiver.Hom.comp_toLoc, ← op_comp,
        pullback.condition])).inv.toNatTrans.app M)]
  have hv₁ : F.mapComp' v₁.op.toLoc (pullback.fst g₁ g₂).op.toLoc
      (pullback.fst g₁ g₂ ≫ v₁).op.toLoc =
      F.mapComp v₁.op.toLoc (pullback.fst g₁ g₂).op.toLoc :=
    F.mapComp'_eq_mapComp _ _
  have hv₂ : F.mapComp' v₂.op.toLoc (pullback.snd g₁ g₂).op.toLoc
      (pullback.snd g₁ g₂ ≫ v₂).op.toLoc =
      F.mapComp v₂.op.toLoc (pullback.snd g₁ g₂).op.toLoc :=
    F.mapComp'_eq_mapComp _ _
  simp only [overlapPairBaseChangeHom, pullHom, hv₁, hv₂, Category.assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Cat.Hom.hom_inv_id_toNatTrans_app,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private lemma pullHom_flatten
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X₁ X₂ W₁ W₂ Q Q' : C}
    (u₁ : W₁ ⟶ X₁) (u₂ : W₂ ⟶ X₂) (v₁ : Q ⟶ W₁) (v₂ : Q ⟶ W₂)
    (s : Q' ⟶ Q) (v₁' : Q' ⟶ W₁) (v₂' : Q' ⟶ W₂)
    (h₁ : s ≫ v₁ = v₁') (h₂ : s ≫ v₂ = v₂')
    (A₁ : F.obj (.mk (op X₁))) (A₂ : F.obj (.mk (op X₂)))
    (ψ : (F.map v₁.op.toLoc).toFunctor.obj ((F.map u₁.op.toLoc).toFunctor.obj A₁) ⟶
      (F.map v₂.op.toLoc).toFunctor.obj ((F.map u₂.op.toLoc).toFunctor.obj A₂)) :
    pullHom
        ((F.mapComp' u₁.op.toLoc v₁.op.toLoc (v₁ ≫ u₁).op.toLoc).hom.toNatTrans.app A₁ ≫
          ψ ≫
          (F.mapComp' u₂.op.toLoc v₂.op.toLoc (v₂ ≫ u₂).op.toLoc).inv.toNatTrans.app A₂)
        s (v₁' ≫ u₁) (v₂' ≫ u₂) (by rw [← h₁, Category.assoc])
          (by rw [← h₂, Category.assoc]) =
      (F.mapComp' u₁.op.toLoc v₁'.op.toLoc (v₁' ≫ u₁).op.toLoc).hom.toNatTrans.app A₁ ≫
        pullHom ψ s v₁' v₂' h₁ h₂ ≫
        (F.mapComp' u₂.op.toLoc v₂'.op.toLoc (v₂' ≫ u₂).op.toLoc).inv.toNatTrans.app A₂ := by
  dsimp only [pullHom]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      u₁.op.toLoc v₁.op.toLoc s.op.toLoc (v₁ ≫ u₁).op.toLoc v₁'.op.toLoc
      (v₁' ≫ u₁).op.toLoc rfl (by rw [← h₁]; rfl) (by rw [← h₁, Category.assoc]; rfl),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
      u₂.op.toLoc v₂.op.toLoc s.op.toLoc (v₂ ≫ u₂).op.toLoc v₂'.op.toLoc
      (v₂' ≫ u₂).op.toLoc rfl (by rw [← h₂]; rfl) (by rw [← h₂, Category.assoc]; rfl)]

set_option backward.isDefEq.respectTransparency false in
private lemma pullHom_flatten_source
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X W B Q Q' : C} (u : W ⟶ X) (v : Q ⟶ W) (f : Q ⟶ B)
    (s : Q' ⟶ Q) (v' : Q' ⟶ W) (f' : Q' ⟶ B)
    (hv : s ≫ v = v') (hf : s ≫ f = f')
    (t : Q ⟶ X) (t' : Q' ⟶ X) (ht : v ≫ u = t) (ht' : v' ≫ u = t')
    (A : F.obj (.mk (op X))) (M : F.obj (.mk (op B)))
    (ψ : (F.map v.op.toLoc).toFunctor.obj ((F.map u.op.toLoc).toFunctor.obj A) ⟶
      (F.map f.op.toLoc).toFunctor.obj M) :
    pullHom
        ((F.mapComp' u.op.toLoc v.op.toLoc t.op.toLoc
          (by rw [← ht]; rfl)).hom.toNatTrans.app A ≫ ψ)
        s t' f' (by rw [← ht', ← hv, Category.assoc, ht]) hf =
      (F.mapComp' u.op.toLoc v'.op.toLoc t'.op.toLoc
        (by rw [← ht']; rfl)).hom.toNatTrans.app A ≫
        pullHom ψ s v' f' hv hf := by
  subst ht ht'
  dsimp only [pullHom]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    u.op.toLoc v.op.toLoc s.op.toLoc (v ≫ u).op.toLoc v'.op.toLoc
    (v' ≫ u).op.toLoc rfl (by rw [← hv]; rfl) (by rw [← hv, Category.assoc]; rfl)]

set_option backward.isDefEq.respectTransparency false in
private lemma pullHom_unflatten_source
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X W B Q Q' : C} (u : W ⟶ X) (v : Q ⟶ W) (f : Q ⟶ B)
    (s : Q' ⟶ Q) (v' : Q' ⟶ W) (f' : Q' ⟶ B)
    (hv : s ≫ v = v') (hf : s ≫ f = f')
    (t : Q ⟶ X) (t' : Q' ⟶ X) (ht : v ≫ u = t) (ht' : v' ≫ u = t')
    (A : F.obj (.mk (op X))) (M : F.obj (.mk (op B)))
    (ψ : (F.map t.op.toLoc).toFunctor.obj A ⟶ (F.map f.op.toLoc).toFunctor.obj M) :
    pullHom
        ((F.mapComp' u.op.toLoc v.op.toLoc t.op.toLoc
          (by rw [← ht]; rfl)).inv.toNatTrans.app A ≫ ψ)
        s v' f' hv hf =
      (F.mapComp' u.op.toLoc v'.op.toLoc t'.op.toLoc
        (by rw [← ht']; rfl)).inv.toNatTrans.app A ≫
        pullHom ψ s t' f' (by rw [← ht', ← hv, Category.assoc, ht]) hf := by
  apply (cancel_epi ((F.mapComp' u.op.toLoc v'.op.toLoc t'.op.toLoc
    (by rw [← ht']; rfl)).hom.toNatTrans.app A)).mp
  rw [← pullHom_flatten_source F u v f s v' f' hv hf t t' ht ht']
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma pullHom_unflatten
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X₁ X₂ W₁ W₂ Q Q' : C}
    (u₁ : W₁ ⟶ X₁) (u₂ : W₂ ⟶ X₂) (v₁ : Q ⟶ W₁) (v₂ : Q ⟶ W₂)
    (s : Q' ⟶ Q) (v₁' : Q' ⟶ W₁) (v₂' : Q' ⟶ W₂)
    (h₁ : s ≫ v₁ = v₁') (h₂ : s ≫ v₂ = v₂')
    (t₁ : Q ⟶ X₁) (t₂ : Q ⟶ X₂) (t₁' : Q' ⟶ X₁) (t₂' : Q' ⟶ X₂)
    (ht₁ : v₁ ≫ u₁ = t₁) (ht₂ : v₂ ≫ u₂ = t₂)
    (ht₁' : v₁' ≫ u₁ = t₁') (ht₂' : v₂' ≫ u₂ = t₂')
    (A₁ : F.obj (.mk (op X₁))) (A₂ : F.obj (.mk (op X₂)))
    (ψ : (F.map t₁.op.toLoc).toFunctor.obj A₁ ⟶
      (F.map t₂.op.toLoc).toFunctor.obj A₂) :
    pullHom
        ((F.mapComp' u₁.op.toLoc v₁.op.toLoc t₁.op.toLoc
          (by rw [← ht₁]; rfl)).inv.toNatTrans.app A₁ ≫ ψ ≫
          (F.mapComp' u₂.op.toLoc v₂.op.toLoc t₂.op.toLoc
            (by rw [← ht₂]; rfl)).hom.toNatTrans.app A₂)
        s v₁' v₂' h₁ h₂ =
      (F.mapComp' u₁.op.toLoc v₁'.op.toLoc t₁'.op.toLoc
        (by rw [← ht₁']; rfl)).inv.toNatTrans.app A₁ ≫
        pullHom ψ s t₁' t₂'
          (by rw [← ht₁', ← h₁, Category.assoc, ht₁])
          (by rw [← ht₂', ← h₂, Category.assoc, ht₂]) ≫
        (F.mapComp' u₂.op.toLoc v₂'.op.toLoc t₂'.op.toLoc
          (by rw [← ht₂']; rfl)).hom.toNatTrans.app A₂ := by
  subst ht₁ ht₂ ht₁' ht₂'
  apply (cancel_epi
    ((F.mapComp' u₁.op.toLoc v₁'.op.toLoc (v₁' ≫ u₁).op.toLoc).hom.toNatTrans.app A₁)).mp
  apply (cancel_mono
    ((F.mapComp' u₂.op.toLoc v₂'.op.toLoc (v₂' ≫ u₂).op.toLoc).inv.toNatTrans.app A₂)).mp
  simp only [Category.assoc]
  rw [← pullHom_flatten F u₁ u₂ v₁ v₂ s v₁' v₂' h₁ h₂]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.assoc, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private lemma pullHom_component
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X X' W W' Z Q : C} (ρ : X' ⟶ X) (v : W ⟶ X) (v' : W' ⟶ X')
    (δ : W' ⟶ W) (f : W ⟶ Z) (f' : W' ⟶ Z)
    (hv : δ ≫ v = v' ≫ ρ) (hf : δ ≫ f = f')
    (A : F.obj (.mk (op X))) (A' : F.obj (.mk (op X')))
    (M : F.obj (.mk (op Z))) (c : A' ⟶ (F.map ρ.op.toLoc).toFunctor.obj A)
    (e : (F.map v.op.toLoc).toFunctor.obj A ⟶ (F.map f.op.toLoc).toFunctor.obj M)
    (e' : (F.map v'.op.toLoc).toFunctor.obj A' ⟶ (F.map f'.op.toLoc).toFunctor.obj M)
    (he : e' = (F.map v'.op.toLoc).toFunctor.map c ≫
      (F.mapComp' ρ.op.toLoc v'.op.toLoc (δ ≫ v).op.toLoc
        (by rw [hv]; rfl)).inv.toNatTrans.app A ≫
      pullHom e δ (δ ≫ v) f' rfl hf)
    (s : Q ⟶ W') (q : Q ⟶ Z) (hq : s ≫ f' = q) :
    pullHom e' s (s ≫ v') q rfl hq =
      (F.map (s ≫ v').op.toLoc).toFunctor.map c ≫
      (F.mapComp' ρ.op.toLoc (s ≫ v').op.toLoc ((s ≫ δ) ≫ v).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]; congr 2
            simp only [Category.assoc, hv])).inv.toNatTrans.app A ≫
      pullHom e (s ≫ δ) ((s ≫ δ) ≫ v) q rfl
        (by rw [Category.assoc, hf, hq]) := by
  rw [he, pullHom_comp _ _ s (s ≫ v') (s ≫ v') q rfl rfl hq,
    pullHom_map]
  rw [pullHom_unflatten_source F ρ v' f' s (s ≫ v') q rfl hq
    (δ ≫ v) ((s ≫ δ) ≫ v) hv.symm (by simp only [Category.assoc, hv])]
  rw [pullHom_pullHom]

set_option backward.isDefEq.respectTransparency false in
private lemma chart_transport
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {ι ι' : Type u} {Y Y' Z : C} {X W : ι → C} {X' W' : ι' → C}
    (f : ∀ d, X d ⟶ Y) (f' : ∀ d, X' d ⟶ Y')
    (α : ι' → ι) (r : Y' ⟶ Y) (ρ : ∀ d, X' d ⟶ X (α d))
    (hr : ∀ d, ρ d ≫ f (α d) = f' d ≫ r)
    (p : Z ⟶ Y) (p' : Z ⟶ Y')
    (v : ∀ d, W d ⟶ X d) (v' : ∀ d, W' d ⟶ X' d)
    (g : ∀ d, W d ⟶ Z) (g' : ∀ d, W' d ⟶ Z)
    (w : ∀ d, v d ≫ f d = g d ≫ p)
    (w' : ∀ d, v' d ≫ f' d = g' d ≫ p')
    (A : ∀ d, F.obj (.mk (op (X d)))) (A' : ∀ d, F.obj (.mk (op (X' d))))
    (M : F.obj (.mk (op Z)))
    (c : ∀ d, (F.map (ρ d).op.toLoc).toFunctor.obj (A (α d)) ≅ A' d)
    (δ : ∀ d, W' d ⟶ W (α d))
    (hδf : ∀ d, δ d ≫ g (α d) = g' d)
    (hδv : ∀ d, δ d ≫ v (α d) = v' d ≫ ρ d)
    (ε : ∀ d, (F.map (v d).op.toLoc).toFunctor.obj (A d) ≅
      (F.map (g d).op.toLoc).toFunctor.obj M)
    (ε' : ∀ d, (F.map (v' d).op.toLoc).toFunctor.obj (A' d) ≅
      (F.map (g' d).op.toLoc).toFunctor.obj M)
    (he : ∀ d, (ε' d).hom = (F.map (v' d).op.toLoc).toFunctor.map (c d).inv ≫
      (F.mapComp' (ρ d).op.toLoc (v' d).op.toLoc
        (δ d ≫ v (α d)).op.toLoc (by rw [hδv]; rfl)).inv.toNatTrans.app (A (α d)) ≫
      pullHom (F := F) (ε (α d)).hom (δ d) (δ d ≫ v (α d)) (g' d) rfl (hδf d))
    (a b : ι')
    (φ : (F.map (pullback.fst (f (α a)) (f (α b))).op.toLoc).toFunctor.obj (A (α a)) ⟶
      (F.map (pullback.snd (f (α a)) (f (α b))).op.toLoc).toFunctor.obj (A (α b)))
    (hs : F.overlapPairBaseChangeSquare f g p v w A
      ((F.toDescentData g).obj M) ε (α a) (α b) φ) :
    F.overlapPairBaseChangeSquare f' g' p' v' w' A'
      ((F.toDescentData g').obj M) ε' a b
      ((F.map (pullback.fst (f' a) (f' b)).op.toLoc).toFunctor.map (c a).inv ≫
        F.overlapPairBaseChangeHom (f (α a)) (f (α b)) r (ρ a) (ρ b)
          (f' a) (f' b) (hr a) (hr b) (A (α a)) (A (α b)) φ ≫
        (F.map (pullback.snd (f' a) (f' b)).op.toLoc).toFunctor.map (c b).hom) := by
  let r₁ := pullback.fst (g (α a)) (g (α b))
  let r₂ := pullback.snd (g (α a)) (g (α b))
  let s₁ := pullback.fst (g' a) (g' b)
  let s₂ := pullback.snd (g' a) (g' b)
  let q := r₁ ≫ g (α a)
  let q' := s₁ ≫ g' a
  let t₁ := (s₁ ≫ δ a) ≫ v (α a)
  let t₂ := (s₂ ≫ δ b) ≫ v (α b)
  let L : pullback (g' a) (g' b) ⟶ pullback (g (α a)) (g (α b)) :=
    pullback.lift (s₁ ≫ δ a) (s₂ ≫ δ b) (by
    dsimp only [s₁, s₂]
    simp only [Category.assoc, hδf]
    exact pullback.condition)
  let H : pullback (g (α a)) (g (α b)) ⟶ pullback (f (α a)) (f (α b)) :=
    pullback.lift (r₁ ≫ v (α a)) (r₂ ≫ v (α b)) (by
    dsimp only [r₁, r₂]
    simp only [Category.assoc, w]
    simp only [← Category.assoc, pullback.condition])
  have hL₁ : L ≫ r₁ = s₁ ≫ δ a := pullback.lift_fst _ _ _
  have hL₂ : L ≫ r₂ = s₂ ≫ δ b := pullback.lift_snd _ _ _
  have hH₁ : H ≫ pullback.fst (f (α a)) (f (α b)) = r₁ ≫ v (α a) :=
    pullback.lift_fst _ _ _
  have hH₂ : H ≫ pullback.snd (f (α a)) (f (α b)) = r₂ ≫ v (α b) :=
    pullback.lift_snd _ _ _
  have hLq : L ≫ q = q' := by
    dsimp only [q, q']
    rw [← Category.assoc, hL₁, Category.assoc, hδf]
  have hLt₁ : L ≫ (r₁ ≫ v (α a)) = t₁ := by rw [← Category.assoc, hL₁]
  have hLt₂ : L ≫ (r₂ ≫ v (α b)) = t₂ := by rw [← Category.assoc, hL₂]
  have hLH₁ : (L ≫ H) ≫ pullback.fst (f (α a)) (f (α b)) = t₁ := by
    rw [Category.assoc, hH₁]
    exact hLt₁
  have hLH₂ : (L ≫ H) ≫ pullback.snd (f (α a)) (f (α b)) = t₂ := by
    rw [Category.assoc, hH₂]
    exact hLt₂
  have hsq := (pair_square_iff F
    (f (α a)) (f (α b)) p (v (α a)) (v (α b))
    (g (α a)) (g (α b)) (w (α a)) (w (α b))
    (A (α a)) (A (α b)) M (ε (α a)) (ε (α b)) φ).mp hs
  have hpulled := congrArg (fun ψ ↦
    pullHom (F := F) ψ L t₁ q' hLt₁ hLq) hsq
  rw [pullHom_comp _ _ L t₁ t₂ q' hLt₁ hLt₂ hLq,
    pullHom_pullHom, pullHom_pullHom, pullHom_pullHom] at hpulled
  change pullHom (F := F) (ε (α a)).hom (L ≫ r₁) t₁ q'
      (by rw [hL₁]) (by rw [Category.assoc, ← hLq]) =
    pullHom (F := F) φ (L ≫ H) t₁ t₂
      hLH₁
      hLH₂ ≫
    pullHom (F := F) (ε (α b)).hom (L ≫ r₂) t₂ q'
      (by rw [hL₂]) (by
        rw [Category.assoc, show r₂ ≫ g (α b) = q from pullback.condition.symm, hLq])
    at hpulled
  simp only [hL₁, hL₂] at hpulled
  have ht₁ : (s₁ ≫ v' a) ≫ ρ a = t₁ := by
    simp only [t₁, Category.assoc, hδv]
  have ht₂ : (s₂ ≫ v' b) ≫ ρ b = t₂ := by
    simp only [t₂, Category.assoc, hδv]
  let β₁ := (F.map ((s₁ ≫ v' a)).op.toLoc).toFunctor.mapIso (c a).symm ≪≫
    (Cat.Hom.toNatIso (F.mapComp' (ρ a).op.toLoc
      (s₁ ≫ v' a).op.toLoc t₁.op.toLoc (by rw [← ht₁]; rfl))).symm.app (A (α a))
  let β₂ := (F.map ((s₂ ≫ v' b)).op.toLoc).toFunctor.mapIso (c b).symm ≪≫
    (Cat.Hom.toNatIso (F.mapComp' (ρ b).op.toLoc
      (s₂ ≫ v' b).op.toLoc t₂.op.toLoc (by rw [← ht₂]; rfl))).symm.app (A (α b))
  have he₁ : pullHom (F := F) (ε' a).hom s₁ (s₁ ≫ v' a) q' rfl rfl =
      β₁.hom ≫ pullHom (F := F) (ε (α a)).hom
        (s₁ ≫ δ a) t₁ q' rfl (by simp only [Category.assoc, hδf]; rfl) := by
    simpa only [β₁, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      Cat.Hom.toNatIso, q', t₁, Category.assoc]
      using pullHom_component F
      (ρ a) (v (α a)) (v' a) (δ a) (g (α a)) (g' a) (hδv a) (hδf a)
      (A (α a)) (A' a) M (c a).inv (ε (α a)).hom (ε' a).hom (he a) s₁ q' rfl
  have he₂ : pullHom (F := F) (ε' b).hom s₂ (s₂ ≫ v' b) q'
        rfl pullback.condition.symm =
      β₂.hom ≫ pullHom (F := F) (ε (α b)).hom
        (s₂ ≫ δ b) t₂ q' rfl (by
          simp only [Category.assoc, hδf]
          exact pullback.condition.symm) := by
    simpa only [β₂, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Cat.Hom.toNatIso, Category.assoc] using
      pullHom_component F
        (ρ b) (v (α b)) (v' b) (δ b) (g (α b)) (g' b) (hδv b) (hδf b)
        (A (α b)) (A' b) M (c b).inv (ε (α b)).hom (ε' b).hom (he b)
        s₂ q' pullback.condition.symm
  let w₁ := pullback.fst (f' a) (f' b)
  let w₂ := pullback.snd (f' a) (f' b)
  let K : pullback (f' a) (f' b) ⟶ pullback (f (α a)) (f (α b)) :=
    pullback.lift (w₁ ≫ ρ a) (w₂ ≫ ρ b) (by
      dsimp only [w₁, w₂]
      rw [Category.assoc, Category.assoc, hr, hr, ← Category.assoc,
        ← Category.assoc, pullback.condition])
  let H' : pullback (g' a) (g' b) ⟶ pullback (f' a) (f' b) :=
    pullback.lift (s₁ ≫ v' a) (s₂ ≫ v' b) (by
      dsimp only [s₁, s₂]
      simp only [Category.assoc, w']
      simp only [← Category.assoc, pullback.condition])
  have hH'₁ : H' ≫ w₁ = s₁ ≫ v' a := pullback.lift_fst _ _ _
  have hH'₂ : H' ≫ w₂ = s₂ ≫ v' b := pullback.lift_snd _ _ _
  have hK₁ : K ≫ pullback.fst (f (α a)) (f (α b)) = w₁ ≫ ρ a :=
    pullback.lift_fst _ _ _
  have hK₂ : K ≫ pullback.snd (f (α a)) (f (α b)) = w₂ ≫ ρ b :=
    pullback.lift_snd _ _ _
  have hKH : H' ≫ K = L ≫ H := by
    apply pullback.hom_ext
    · rw [Category.assoc, hK₁, ← Category.assoc, hH'₁, hLH₁]
      exact ht₁
    · rw [Category.assoc, hK₂, ← Category.assoc, hH'₂, hLH₂]
      exact ht₂
  let φ' := (F.map (w₁).op.toLoc).toFunctor.map (c a).inv ≫
    F.overlapPairBaseChangeHom
      (f (α a)) (f (α b)) r (ρ a) (ρ b) (f' a) (f' b)
      (hr a) (hr b) (A (α a)) (A (α b)) φ ≫
    (F.map (w₂).op.toLoc).toFunctor.map (c b).hom
  have hφ' : pullHom (F := F) φ' H' (s₁ ≫ v' a) (s₂ ≫ v' b)
        hH'₁ hH'₂ =
      β₁.hom ≫ pullHom (F := F) φ (L ≫ H) t₁ t₂
        hLH₁
        hLH₂ ≫
      β₂.inv := by
    dsimp only [φ']
    rw [pullHom_comp _ _ H' (s₁ ≫ v' a) (s₁ ≫ v' a) (s₂ ≫ v' b)
        hH'₁ hH'₁ hH'₂,
      pullHom_comp _ _ H' (s₁ ≫ v' a) (s₂ ≫ v' b) (s₂ ≫ v' b)
        hH'₁ hH'₂ hH'₂, pullHom_map, pullHom_map]
    have hw₁ : F.mapComp (ρ a).op.toLoc w₁.op.toLoc =
        F.mapComp' (ρ a).op.toLoc w₁.op.toLoc (w₁ ≫ ρ a).op.toLoc :=
      (F.mapComp'_eq_mapComp _ _).symm
    have hw₂ : F.mapComp (ρ b).op.toLoc w₂.op.toLoc =
        F.mapComp' (ρ b).op.toLoc w₂.op.toLoc (w₂ ≫ ρ b).op.toLoc :=
      (F.mapComp'_eq_mapComp _ _).symm
    dsimp only [overlapPairBaseChangeHom]
    rw [hw₁, hw₂,
      pullHom_unflatten F (ρ a) (ρ b) w₁ w₂
        H' (s₁ ≫ v' a) (s₂ ≫ v' b) hH'₁ hH'₂
        (w₁ ≫ ρ a) (w₂ ≫ ρ b) t₁ t₂ rfl rfl ht₁ ht₂,
      pullHom_pullHom]
    simp only [← hKH, β₁, β₂, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    rfl
  apply (pair_square_iff F (f' a) (f' b)
    p' (v' a) (v' b) (g' a) (g' b) (w' a)
    (w' b) (A' a) (A' b) M (ε' a) (ε' b) φ').mpr
  change pullHom (F := F) (ε' a).hom s₁ (s₁ ≫ v' a) q' rfl rfl =
    pullHom (F := F) φ' H' (s₁ ≫ v' a) (s₂ ≫ v' b) hH'₁ hH'₂ ≫
    pullHom (F := F) (ε' b).hom s₂ (s₂ ≫ v' b) q'
      rfl pullback.condition.symm
  rw [he₁, he₂, hφ']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hpulled]


end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

private lemma modules_map_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : X.Modules} (ψ : A ⟶ B) :
    (modulesPseudofunctor.map f.op.toLoc).toFunctor.map ψ =
      (Scheme.Modules.pullback f).map ψ := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma modules_component_eq
    {X X' W W' Z : Scheme.{u}} (ρ : X' ⟶ X) (v : W ⟶ X) (v' : W' ⟶ X')
    (δ : W' ⟶ W) (f : W ⟶ Z) (f' : W' ⟶ Z)
    (hv : δ ≫ v = v' ≫ ρ) (hf : δ ≫ f = f')
    (A : X.Modules) (A' : X'.Modules) (M : Z.Modules)
    (c : (Scheme.Modules.pullback ρ).obj A ≅ A')
    (e : (Scheme.Modules.pullback v).obj A ≅ (Scheme.Modules.pullback f).obj M) :
    ((Scheme.Modules.pullback v').mapIso c.symm ≪≫
      pullbackCompOfEq v' ρ (δ ≫ v) hv.symm A ≪≫
      (pullbackCompOfEq δ v (δ ≫ v) rfl A).symm ≪≫
      (Scheme.Modules.pullback δ).mapIso e ≪≫
      pullbackCompOfEq δ f f' hf M).hom =
    (modulesPseudofunctor.map v'.op.toLoc).toFunctor.map c.inv ≫
      (modulesPseudofunctor.mapComp' ρ.op.toLoc v'.op.toLoc
        (δ ≫ v).op.toLoc (by rw [hv]; rfl)).inv.toNatTrans.app A ≫
      pullHom (F := modulesPseudofunctor) e.hom δ (δ ≫ v) f' rfl hf := by
  have h₁ := modulesPseudofunctor_mapComp'_inv_app_eq ρ v' (δ ≫ v) hv.symm A
  have h₂ := modulesPseudofunctor_mapComp'_hom_app_eq v δ (δ ≫ v) rfl A
  have h₃ := modulesPseudofunctor_mapComp'_inv_app_eq f δ f' hf M
  simp only [pullHom, h₁, h₂, h₃, modules_map_map,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Transport a pair square along a diagram of cover charts, using specified chart isomorphisms.
Source: Stacks Project, Tag 01ZR, first proof, successive restriction; Mathlib
Sites/Descent/IsPrestack.lean, pullHom_pullHom.
(blueprint: lem-pc-overlap-pair-square-chart-transport).

Proof: Write K for the map from the later stage overlap to the earlier stage overlap,
constructed by pullback.lift from fst followed by ρ a and snd followed by ρ b. Write L
for the analogous map between the limit overlaps, using δ a and δ b. Their lift
conditions follow from hr and hδf. Apply the module pullback functor along L to hs and
conjugate its ends by the pullback composition comparisons for the overlap projections.
Naturality of mapComp moves the pulled ε components through these comparisons.
DescentData.pullHom_hom for the restriction datum of M identifies its pulled transition
with the later limit transition, using hδf.

The two composites from the later limit overlap to the earlier stage overlap, through L
and the old limit-to-stage overlap map or through the new limit-to-stage overlap map and K,
are equal: their fst and snd projections agree by hδv, so pullback.hom_ext applies.
The identity pullHom_pullHom therefore identifies the middle map with the pullback of
the base-changed stage map. Apply the mapComp pentagon to the three successive projections,
and naturality to the chart isomorphisms c. Cancel each adjacent composition comparison
with its inverse. This puts the pullbacks of c a.inv and c b.hom at the two ends of the
stage map, giving exactly the explicit map in the conclusion. The remaining component
comparisons are the five displayed factors in hε; replace them with ε' using hε. The
resulting equality is the later overlapPairSquare. These are universal pullback maps and
functorial identities, so empty charts, empty overlaps and arbitrary index maps α cause
no exceptions. No identity or cocycle equation for φ is used. -/
theorem overlap_pair_square_chart_transport
    {Y Y' Z : Scheme.{u}} (V : Y.OpenCover.{u}) (V' : Y'.OpenCover.{u})
    (α : V'.I₀ → V.I₀) (r : Y' ⟶ Y) (ρ : ∀ d, V'.X d ⟶ V.X (α d))
    (hr : ∀ d, ρ d ≫ V.f (α d) = V'.f d ≫ r)
    (p : Z ⟶ Y) (p' : Z ⟶ Y')
    (A : (d : V.I₀) → (V.X d).Modules)
    (A' : (d : V'.I₀) → (V'.X d).Modules) (M : Z.Modules)
    (c : ∀ d, (Scheme.Modules.pullback (ρ d)).obj (A (α d)) ≅ A' d)
    (δ : ∀ d, (V'.pullback₁ p').X d ⟶ (V.pullback₁ p).X (α d))
    (hδf : ∀ d, δ d ≫ (V.pullback₁ p).f (α d) = (V'.pullback₁ p').f d)
    (hδv : ∀ d, δ d ≫ V.pullbackHom p (α d) = V'.pullbackHom p' d ≫ ρ d)
    (ε : ∀ d, (Scheme.Modules.pullback (V.pullbackHom p d)).obj (A d) ≅
      (Scheme.Modules.pullback ((V.pullback₁ p).f d)).obj M)
    (ε' : ∀ d, (Scheme.Modules.pullback (V'.pullbackHom p' d)).obj (A' d) ≅
      (Scheme.Modules.pullback ((V'.pullback₁ p').f d)).obj M)
    (hε : ε' =
    (fun d ↦ (Scheme.Modules.pullback (V'.pullbackHom p' d)).mapIso (c d).symm ≪≫
      pullbackCompOfEq (V'.pullbackHom p' d) (ρ d)
        (δ d ≫ V.pullbackHom p (α d)) (hδv d).symm (A (α d)) ≪≫
      (pullbackCompOfEq (δ d) (V.pullbackHom p (α d))
        (δ d ≫ V.pullbackHom p (α d)) rfl (A (α d))).symm ≪≫
      (Scheme.Modules.pullback (δ d)).mapIso (ε (α d)) ≪≫
      pullbackCompOfEq (δ d) ((V.pullback₁ p).f (α d))
        ((V'.pullback₁ p').f d) (hδf d) M))
    (a b : V'.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (V.f (α a)) (V.f (α b)))).obj
        (A (α a)) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f (α a)) (V.f (α b)))).obj
        (A (α b)))
    (hs : overlapPairSquare V A p
      ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M) ε (α a) (α b) φ) :
    overlapPairSquare V' A' p'
      ((modulesPseudofunctor.toDescentData (V'.pullback₁ p').f).obj M)
      ε' a b
      ((Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).map (c a).inv ≫
        modulesPseudofunctor.overlapPairBaseChangeHom
          (V.f (α a)) (V.f (α b)) r (ρ a) (ρ b) (V'.f a) (V'.f b)
          (hr a) (hr b) (A (α a)) (A (α b)) φ ≫
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).map (c b).hom) := by
  refine Pseudofunctor.chart_transport
    (C := Scheme.{u}) (ι := V.I₀) (ι' := V'.I₀) (X := V.X) (X' := V'.X)
    (W := (V.pullback₁ p).X) (W' := (V'.pullback₁ p').X)
    modulesPseudofunctor V.f V'.f α r ρ hr p p'
    (fun d ↦ V.pullbackHom p d) (fun d ↦ V'.pullbackHom p' d)
    (V.pullback₁ p).f (V'.pullback₁ p').f
    (fun d ↦ V.pullbackHom_map p d) (fun d ↦ V'.pullbackHom_map p' d)
    A A' M c δ hδf hδv ε ε' ?_ a b φ hs
  intro d
  exact (congrArg Iso.hom (congrFun hε d)).trans
    (modules_component_eq (ρ d) (V.pullbackHom p (α d)) (V'.pullbackHom p' d)
      (δ d) ((V.pullback₁ p).f (α d)) ((V'.pullback₁ p').f d)
      (hδv d) (hδf d) (A (α d)) (A' d) M (c d) (ε (α d)))


end AlgebraicGeometry
