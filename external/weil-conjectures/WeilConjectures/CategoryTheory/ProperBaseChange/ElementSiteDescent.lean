/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction

/-!
# Descent along the element site

Source: Stacks Project, Tag 0791, lemma-localize-topos-site; sites-modules.tex Tag 04J4
(blueprint: lem-weil-pbc-element-site-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def liftElement {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) (e : A.obj.Elementsᵒᵖ) {V : C}
    (f : V ⟶ (elementProjection A).obj e) : A.obj.Elementsᵒᵖ :=
  op (A.obj.elementsMk (op V) (A.obj.map f.op e.unop.2))

private def liftElementHom {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) (e : A.obj.Elementsᵒᵖ) {V : C}
    (f : V ⟶ (elementProjection A).obj e) : liftElement A e f ⟶ e :=
  (Functor.Elements.homMk (x := e.unop) f.op rfl).op

private theorem projection_push_pull {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (e : A.obj.Elementsᵒᵖ) (S : Sieve ((elementProjection A).obj e)) :
    (S.functorPullback (elementProjection A)).functorPushforward (elementProjection A) = S := by
  apply le_antisymm
  · exact Sieve.functorPullback_pushforward_le _ _
  · intro V f hf
    exact ⟨liftElement A e f, liftElementHom A e f, 𝟙 V, hf, by
      simp [liftElementHom, elementProjection]⟩

private theorem projection_compatible {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    CompatiblePreserving J (elementProjection A) where
  compatible F {Z T x} hx {Y₁ Y₂ W} f₁ f₂ {g₁ g₂} hg₁ hg₂ h := by
    let W' := liftElement A Y₁ f₁
    let a : W' ⟶ Y₁ := liftElementHom A Y₁ f₁
    have hs : A.obj.map f₂.op Y₂.unop.2 = A.obj.map f₁.op Y₁.unop.2 := by
      calc
        _ = A.obj.map (g₂.unop.1 ≫ f₂.op) Z.unop.2 := by
          rw [Functor.map_comp_apply, g₂.unop.2]
          rfl
        _ = A.obj.map (g₁.unop.1 ≫ f₁.op) Z.unop.2 := by
          exact congrArg (fun k ↦ A.obj.map k.op Z.unop.2) h.symm
        _ = _ := by rw [Functor.map_comp_apply, g₁.unop.2]; rfl
    let b : W' ⟶ Y₂ :=
      (Functor.Elements.homMk (x := Y₂.unop) (y := W'.unop) f₂.op hs).op
    exact hx a b hg₁ hg₂ (by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      exact congrArg Quiver.Hom.op h)

private theorem projection_mem_push {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (e : A.obj.Elementsᵒᵖ) (S : Sieve e) {V : C}
    (f : V ⟶ (elementProjection A).obj e) :
    S.functorPushforward (elementProjection A) f ↔ S (liftElementHom A e f) := by
  constructor
  · rintro ⟨d, g, k, hg, hk⟩
    let a : liftElement A e f ⟶ d :=
      (Functor.Elements.homMk (x := d.unop) k.op (by
        change A.obj.map k.op (d.unop.2) = A.obj.map f.op e.unop.2
        rw [← g.unop.2]
        have h := congrArg Quiver.Hom.op hk.symm
        change g.unop.1 ≫ k.op = f.op at h
        exact (A.obj.map_comp_apply g.unop.1 k.op e.unop.2).symm.trans
          (congrArg (fun q ↦ A.obj.map q e.unop.2) h))).op
    have ha : a ≫ g = liftElementHom A e f := by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      exact congrArg Quiver.Hom.op hk.symm
    rw [← ha]
    exact S.downward_closed hg a
  · intro hf
    exact ⟨liftElement A e f, liftElementHom A e f, 𝟙 V, hf, by
      simp [elementProjection, liftElementHom]⟩

private theorem projection_pull_push {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (e : A.obj.Elementsᵒᵖ) (S : Sieve e) :
    (S.functorPushforward (elementProjection A)).functorPullback (elementProjection A) = S := by
  apply le_antisymm
  · intro d g hg
    obtain ⟨d', g', k, hg', hk⟩ := hg
    let a : d ⟶ d' := (Functor.Elements.homMk (x := d'.unop) (y := d.unop) k.op (by
      change A.obj.map k.op d'.unop.2 = d.unop.2
      rw [← g'.unop.2]
      have h := congrArg Quiver.Hom.op hk.symm
      change g'.unop.1 ≫ k.op = g.unop.1 at h
      exact ((A.obj.map_comp_apply g'.unop.1 k.op e.unop.2).symm.trans
        (congrArg (fun q ↦ A.obj.map q e.unop.2) h)).trans g.unop.2)).op
    have ha : a ≫ g' = g := by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      exact congrArg Quiver.Hom.op hk.symm
    rw [← ha]
    exact S.downward_closed hg' a
  · exact Sieve.le_functorPushforward_pullback _ _

private theorem projection_push_pullback {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    {e d : A.obj.Elementsᵒᵖ} (f : d ⟶ e) (S : Sieve e) :
    (S.pullback f).functorPushforward (elementProjection A) =
      (S.functorPushforward (elementProjection A)).pullback ((elementProjection A).map f) := by
  apply (Function.LeftInverse.injective (projection_push_pull A d))
  rw [Sieve.functorPullback_pullback, projection_pull_push, projection_pull_push]

private def liftedTopology {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    GrothendieckTopology A.obj.Elementsᵒᵖ where
  sieves e := {S | S.functorPushforward (elementProjection A) ∈ J _}
  top_mem' e := by simp
  pullback_stable' e d S f hS := by
    change (S.pullback f).functorPushforward (elementProjection A) ∈ J _
    rw [projection_push_pullback]
    exact J.pullback_stable _ hS
  transitive' e S hS T hT := by
    apply J.transitive hS
    intro V f hf
    rw [projection_mem_push] at hf
    have h := hT hf
    change (T.pullback (liftElementHom A e f)).functorPushforward (elementProjection A) ∈ J _ at h
    rw [projection_push_pullback] at h
    exact h

private theorem liftedTopology_eq_restricted {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    liftedTopology A = (elementProjection A).restrictedTopology J := by
  apply le_antisymm
  · intro e S hS
    exact Functor.mem_restrictedTopology_of_functorPushforward_mem hS
  · change (J.toPrecoverage.comap (elementProjection A)).toGrothendieck ≤ liftedTopology A
    rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro e S hS
    rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff] at hS
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    change (Sieve.generate S).functorPushforward (elementProjection A) ∈ J _
    rwa [← Sieve.generate_map_eq_functorPushforward]

private theorem projection_topology {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    elementTopology A = (elementProjection A).restrictedTopology J := by
  have : (elementProjection A).IsContinuous (liftedTopology A) J :=
    Functor.isContinuous_of_coverPreserving (projection_compatible A) ⟨fun h ↦ h⟩
  have : (elementProjection A).IsContinuous ((elementProjection A).restrictedTopology J) J := by
    rw [← liftedTopology_eq_restricted A]
    infer_instance
  exact (Functor.restrictedTopology_eq_inducedTopology).symm

private theorem projection_cocontinuous {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    Functor.IsCocontinuous (elementProjection A) (elementTopology A) J where
  cover_lift {e} S hS := by
    rw [projection_topology, ← liftedTopology_eq_restricted]
    change (S.functorPullback (elementProjection A)).functorPushforward
      (elementProjection A) ∈ J _
    rwa [projection_push_pull]

private theorem elementMap_compatible {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {B A : Sheaf J (Type u)} (b : B ⟶ A) :
    CompatiblePreserving (elementTopology A) (elementMap b) where
  compatible F {Z T x} hx {Y₁ Y₂ W} f₁ f₂ {g₁ g₂} hg₁ hg₂ h := by
    let k₁ := (elementProjection A).map f₁
    let k₂ := (elementProjection A).map f₂
    let W' := liftElement B Y₁ k₁
    let a : W' ⟶ Y₁ := liftElementHom B Y₁ k₁
    have hs : B.obj.map k₂.op Y₂.unop.2 = B.obj.map k₁.op Y₁.unop.2 := by
      calc
        _ = B.obj.map (g₂.unop.1 ≫ k₂.op) Z.unop.2 := by
          rw [Functor.map_comp_apply, g₂.unop.2]
          rfl
        _ = B.obj.map (g₁.unop.1 ≫ k₁.op) Z.unop.2 := by
          exact congrArg (fun q ↦ B.obj.map q.op Z.unop.2)
            ((elementProjection A).congr_map h).symm
        _ = _ := by rw [Functor.map_comp_apply, g₁.unop.2]; rfl
    let c : W' ⟶ Y₂ :=
      (Functor.Elements.homMk (x := Y₂.unop) (y := W'.unop) k₂.op hs).op
    let e : (elementMap b).obj W' ≅ W :=
      (Functor.Elements.isoMk (x := unop W) (y := unop ((elementMap b).obj W'))
        (Iso.refl _) (by
        change A.obj.map (𝟙 _) W.unop.2 = b.hom.app _ (B.obj.map k₁.op Y₁.unop.2)
        rw [Functor.map_id_apply]
        exact f₁.unop.2.symm.trans (NatTrans.naturality_apply b.hom k₁.op Y₁.unop.2).symm)).op
    have h₁ : e.inv ≫ (elementMap b).map a = f₁ := by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      change f₁.unop.1 ≫ (𝟙 _) = f₁.unop.1
      simp
    have h₂ : e.inv ≫ (elementMap b).map c = f₂ := by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      change f₂.unop.1 ≫ (𝟙 _) = f₂.unop.1
      simp
    rw [← h₁, ← h₂]
    simp only [op_comp, Functor.map_comp, types_comp_apply]
    apply congrArg (F.obj.map e.inv.op)
    exact hx a c hg₁ hg₂ (by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      exact congrArg Quiver.Hom.op ((elementProjection A).congr_map h))

private theorem elementMap_continuous {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {B A : Sheaf J (Type u)} (b : B ⟶ A) :
    Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A) := by
  apply Functor.isContinuous_of_coverPreserving (elementMap_compatible b)
  constructor
  intro e S hS
  rw [projection_topology, ← liftedTopology_eq_restricted] at hS ⊢
  change (S.functorPushforward (elementMap b)).functorPushforward
    (elementProjection A) ∈ J _
  rw [← Sieve.functorPushforward_comp]
  exact hS

private def fibreSubfunctor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A : Sheaf J (Type u)}
    (X : CostructuredArrow (𝟭 (Sheaf J (Type u))) A) :
    Subfunctor ((elementProjection A).op ⋙ X.left.obj) where
  obj e := {x | X.hom.hom.app e.unop.unop.1 x = e.unop.unop.2}
  map {e e'} g x hx := by
    change X.hom.hom.app _ x = _ at hx
    exact ((NatTrans.naturality_apply X.hom.hom g.unop.unop.1 x).trans
      (congrArg _ hx)).trans g.unop.unop.2

private theorem fibre_isSheaf {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A : Sheaf J (Type u)}
    (X : CostructuredArrow (𝟭 (Sheaf J (Type u))) A) :
    Presheaf.IsSheaf (elementTopology A) ((elementFibrePresheafFunctor A).obj X) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  change Presieve.IsSheaf (elementTopology A) (fibreSubfunctor X).toFunctor
  have hX := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((elementSheafPullback A).obj X.left).property
  apply (Subfunctor.isSheaf_iff _ hX).mpr
  intro e x hx
  let G := (elementSheafPullback A).obj A
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated _ hx).ext
  intro d g hg
  change A.obj.map g.unop.1 (X.hom.hom.app _ x) = A.obj.map g.unop.1 e.unop.unop.2
  rw [← NatTrans.naturality_apply, g.unop.2]
  exact hg

private def fibreFunctor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    CostructuredArrow (𝟭 (Sheaf J (Type u))) A ⥤ Sheaf (elementTopology A) (Type u) where
  obj X := ⟨(elementFibrePresheafFunctor A).obj X, fibre_isSheaf X⟩
  map f := ⟨(elementFibrePresheafFunctor A).map f⟩

private theorem pair_ext {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A : Sheaf J (Type u)}
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) {U : Cᵒᵖ} {s t : A.obj.obj U}
    {x : H.obj (elementObj A U s)} {y : H.obj (elementObj A U t)}
    (h : s = t) (hx : H.map (eqToHom (by rw [h])) x = y) :
    (⟨s, x⟩ : Σ s : A.obj.obj U, H.obj (elementObj A U s)) = ⟨t, y⟩ := by
  subst t
  have hx' : x = y := by simpa using hx
  cases hx'
  rfl

private theorem element_eqToHom_val {D : Type u} [SmallCategory D]
    (F : D ⥤ Type u) {x y : F.Elements} (h : x = y) :
    (eqToHom h : x ⟶ y).hom = eqToHom (congrArg Functor.Elements.obj h) := by
  cases h
  rfl

private def pairPresheaf {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Type u where
  obj U := Σ s : A.obj.obj U, H.obj (elementObj A U s)
  map {U V} f := ↾fun x ↦ ⟨A.obj.map f x.1, H.map (elementObjMap A f x.1) x.2⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, x⟩
    apply pair_ext H (A.obj.map_id_apply U s)
    simp only [← Functor.map_comp_apply]
    have h : elementObjMap A (𝟙 U) s ≫ eqToHom (by simp) = 𝟙 (elementObj A U s) := by
      apply Quiver.Hom.unop_inj
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      simp [elementObjMap, eqToHom_unop, element_eqToHom_val]
    rw [h, Functor.map_id_apply]
  map_comp {U V W} f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, x⟩
    apply pair_ext H (A.obj.map_comp_apply f g s)
    change H.map (eqToHom _) (H.map (elementObjMap A (f ≫ g) s) x) =
      H.map (elementObjMap A g (A.obj.map f s)) (H.map (elementObjMap A f s) x)
    simp only [← Functor.map_comp_apply]
    apply congrArg (fun k ↦ H.map k x)
    apply Quiver.Hom.unop_inj
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    simp [elementObjMap, eqToHom_unop, element_eqToHom_val]

private def fibrePreimageMap {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A : Sheaf J (Type u)}
    {X Y : CostructuredArrow (𝟭 (Sheaf J (Type u))) A}
    (α : (fibreFunctor A).obj X ⟶ (fibreFunctor A).obj Y)
    (U : Cᵒᵖ) (x : X.left.obj.obj U) : Y.left.obj.obj U :=
  (α.hom.app (elementObj A U (X.hom.hom.app U x)) ⟨x, rfl⟩).val

private theorem fibrePreimageMap_eq {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A : Sheaf J (Type u)}
    {X Y : CostructuredArrow (𝟭 (Sheaf J (Type u))) A}
    (α : (fibreFunctor A).obj X ⟶ (fibreFunctor A).obj Y)
    (U : Cᵒᵖ) (s : A.obj.obj U) (x : X.left.obj.obj U) (hx : X.hom.hom.app U x = s) :
    (α.hom.app (elementObj A U s) ⟨x, hx⟩).val = fibrePreimageMap α U x := by
  subst s
  rfl

private def fibrePreimage {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {A : Sheaf J (Type u)}
    {X Y : CostructuredArrow (𝟭 (Sheaf J (Type u))) A}
    (α : (fibreFunctor A).obj X ⟶ (fibreFunctor A).obj Y) : X ⟶ Y :=
  CostructuredArrow.homMk
    (show X.left ⟶ Y.left from
      ⟨{ app U := ↾(fibrePreimageMap α U)
         naturality := by
           intro U V g
           ext x
           have h := NatTrans.naturality_apply α.hom
             (elementObjMap A g (X.hom.hom.app U x)) ⟨x, rfl⟩
           have hh := congrArg Subtype.val h
           change (α.hom.app (elementObj A V (A.obj.map g (X.hom.hom.app U x)))
             ⟨X.left.obj.map g x, _⟩).val = Y.left.obj.map g (fibrePreimageMap α U x) at hh
           rw [fibrePreimageMap_eq] at hh
           exact hh }⟩) (by
      ext U x
      exact (α.hom.app (elementObj A U (X.hom.hom.app U x)) ⟨x, rfl⟩).property)

private def fibreFullyFaithful {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    (fibreFunctor A).FullyFaithful where
  preimage := fibrePreimage
  map_preimage α := by
    ext e x
    apply Subtype.ext
    exact (fibrePreimageMap_eq α e.unop.unop.1 e.unop.unop.2 x.val x.property).symm
  preimage_map f := by
    ext U x
    rfl

private def pairEmbedding {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) (e : A.obj.Elementsᵒᵖ)
    (x : H.obj (op e)) : (pairPresheaf A H).obj (op ((elementProjection A).obj e)) :=
  ⟨e.unop.2, x⟩

private theorem pairEmbedding_injective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) (e : A.obj.Elementsᵒᵖ) :
    Function.Injective (pairEmbedding A H e) := by
  intro x y h
  exact (Sigma.mk.inj h).2.eq

private theorem pairEmbedding_map {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) {e d : A.obj.Elementsᵒᵖ} (g : d ⟶ e)
    (x : H.obj (op e)) :
    pairEmbedding A H d (H.map g.op x) =
      (pairPresheaf A H).map ((elementProjection A).map g).op
        (pairEmbedding A H e x) := by
  apply pair_ext H g.unop.2.symm
  change H.map (eqToHom _) (H.map g.op x) = H.map (elementObjMap A _ _) x
  rw [← Functor.map_comp_apply]
  apply congrArg (fun k ↦ H.map k x)
  apply Quiver.Hom.unop_inj
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  simp [elementObjMap, eqToHom_unop, element_eqToHom_val]

private def pairValue {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) (e : A.obj.Elementsᵒᵖ)
    (z : (pairPresheaf A H).obj (op ((elementProjection A).obj e)))
    (h : z.1 = e.unop.2) : H.obj (op e) :=
  H.map (eqToHom (congrArg (elementObj A _) h)) z.2

private theorem pairEmbedding_value {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : A.obj.Elementsᵒᵖᵒᵖ ⥤ Type u) (e : A.obj.Elementsᵒᵖ)
    (z : (pairPresheaf A H).obj (op ((elementProjection A).obj e)))
    (h : z.1 = e.unop.2) :
    pairEmbedding A H e (pairValue A H e z h) = z := by
  apply pair_ext H h.symm
  change H.map (eqToHom _) (H.map (eqToHom _) z.2) = z.2
  simp only [← Functor.map_comp_apply, eqToHom_trans, eqToHom_refl, Functor.map_id_apply]

private theorem pair_isSheaf {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : Sheaf (elementTopology A) (Type u)) :
    Presheaf.IsSheaf J (pairPresheaf A H.obj) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro U S hS x hx
  let xs : Presieve.FamilyOfElements A.obj S.arrows := fun V f hf ↦ (x f hf).1
  have hxs : xs.Compatible := by
    intro V W Z f g a b ha hb hab
    exact congrArg Sigma.fst (hx f g ha hb hab)
  have hA := (isSheaf_iff_isSheaf_of_type _ _).mp A.property
  let s := (hA S hS).amalgamate xs hxs
  have hs : xs.IsAmalgamation s := (hA S hS).isAmalgamation hxs
  let e : A.obj.Elementsᵒᵖ := op (A.obj.elementsMk (op U) s)
  let T := S.functorPullback (elementProjection A) (X := e)
  have hT : T ∈ elementTopology A e :=
    @Functor.IsCocontinuous.cover_lift _ _ _ _ _ _ _ (projection_cocontinuous A) e S hS
  let y : Presieve.FamilyOfElements H.obj T.arrows := fun d g hg ↦
    pairValue A H.obj d (x ((elementProjection A).map g) hg)
      ((hs ((elementProjection A).map g) hg).symm.trans g.unop.2)
  have hy : y.Compatible := by
    intro d d' W f g a b ha hb hab
    apply pairEmbedding_injective A H.obj W
    rw [pairEmbedding_map, pairEmbedding_map]
    change (pairPresheaf A H.obj).map _ (pairEmbedding A H.obj d
      (pairValue A H.obj d _ _)) =
      (pairPresheaf A H.obj).map _ (pairEmbedding A H.obj d'
        (pairValue A H.obj d' _ _))
    rw [pairEmbedding_value, pairEmbedding_value]
    exact hx ((elementProjection A).map f) ((elementProjection A).map g) ha hb
      (by simpa only [Functor.map_comp] using (elementProjection A).congr_map hab)
  have hH := (isSheaf_iff_isSheaf_of_type _ _).mp H.property
  obtain ⟨l, hl, huniq⟩ := hH T hT y hy
  refine ⟨pairEmbedding A H.obj e l, ?_, ?_⟩
  · intro V f hf
    have he := congrArg (pairEmbedding A H.obj (liftElement A e f))
      (hl (liftElementHom A e f) hf)
    rw [pairEmbedding_map] at he
    change (pairPresheaf A H.obj).map f.op (pairEmbedding A H.obj e l) =
      pairEmbedding A H.obj (liftElement A e f)
        (pairValue A H.obj (liftElement A e f) _ _) at he
    rw [pairEmbedding_value] at he
    exact he
  · intro t ht
    have hts : t.1 = s := (hA S hS).isSeparatedFor xs t.1 s
      (fun V f hf ↦ congrArg Sigma.fst (ht f hf)) hs
    let v := pairValue A H.obj e t hts
    have hv : y.IsAmalgamation v := by
      intro d g hg
      apply pairEmbedding_injective A H.obj d
      rw [pairEmbedding_map]
      change (pairPresheaf A H.obj).map _
        (pairEmbedding A H.obj e (pairValue A H.obj e t hts)) =
        pairEmbedding A H.obj d (pairValue A H.obj d _ _)
      rw [pairEmbedding_value, pairEmbedding_value]
      exact ht ((elementProjection A).map g) hg
    calc
      t = pairEmbedding A H.obj e v := (pairEmbedding_value A H.obj e t hts).symm
      _ = pairEmbedding A H.obj e l := congrArg (pairEmbedding A H.obj e) (huniq v hv)

private def pairSlice {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : Sheaf (elementTopology A) (Type u)) :
    CostructuredArrow (𝟭 (Sheaf J (Type u))) A :=
  CostructuredArrow.mk
    (show (⟨pairPresheaf A H.obj, pair_isSheaf A H⟩ : Sheaf J (Type u)) ⟶ A from
      ⟨{ app U := ↾Sigma.fst }⟩)

private def pairFibreIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u))
    (H : Sheaf (elementTopology A) (Type u)) :
    (fibreFunctor A).obj (pairSlice A H) ≅ H :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun e ↦ Equiv.toIso
    { toFun := fun z ↦ pairValue A H.obj e.unop z.val z.property
      invFun := fun x ↦ ⟨pairEmbedding A H.obj e.unop x, rfl⟩
      left_inv := fun z ↦ Subtype.ext (pairEmbedding_value A H.obj e.unop z.val z.property)
      right_inv := fun x ↦ by
        change H.obj.map (𝟙 e) x = x
        exact H.obj.map_id_apply e x }) (by
    intro e d g
    ext z
    change pairValue A H.obj d.unop
      ((pairPresheaf A H.obj).map ((elementProjection A).map g.unop).op z.val)
        (by exact (congrArg (A.obj.map g.unop.unop.1) z.property).trans g.unop.unop.2) =
      H.obj.map g (pairValue A H.obj e.unop z.val z.property)
    apply pairEmbedding_injective A H.obj d.unop
    rw [pairEmbedding_value]
    change _ = pairEmbedding A H.obj d.unop
      (H.obj.map g.unop.op (pairValue A H.obj e.unop z.val z.property))
    rw [pairEmbedding_map, pairEmbedding_value]))

private theorem fibre_essSurj {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J (Type u)) :
    (fibreFunctor A).EssSurj where
  mem_essImage H := ⟨pairSlice A H, ⟨pairFibreIso A H⟩⟩

/-- Descent along the element site.

Source: literature/stacks-project/sites.tex, Tag 0791, lemma-localize-topos-site;
sites-modules.tex Tag 04J4
(blueprint: lem-weil-pbc-element-site-descent).
Proof: Lift every arrow v:V→U uniquely below (U,s) to (V,A(v)s)→(U,s). Sieves below these objects
identify with sieves below U, compatibly with pullback and transitivity. The resulting topology
is restrictedTopology, and precomposition preserves sheaves, so Mathlib
restrictedTopology_eq_inducedTopology identifies it with J_A. Lift covering sieves to prove
cocontinuity. Fibre sections glue uniquely in F; their images agree with s by separatedness of
A. Conversely pairs (s,x) glue by first gluing s in A and then x on the lifted element cover.
The maps x↦(p(x),x) and fibre evaluation give inverse natural isomorphisms, including all
restrictions. A sheaf map B→A carries lifted covering families to lifted covering families and
preserves this sheaf gluing condition, giving continuity of the element map. Empty fibres and
empty covers satisfy the same sheaf condition. -/
theorem element_site_descent
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) :
    elementTopology A = (elementProjection A).restrictedTopology J ∧
    Functor.IsCocontinuous (elementProjection A) (elementTopology A) J ∧
    (∃ e : Sheaf (elementTopology A) (Type u) ≌
        CostructuredArrow (𝟭 (Sheaf J (Type u))) A,
      Nonempty (e.inverse ⋙ sheafToPresheaf (elementTopology A) (Type u) ≅
        elementFibrePresheafFunctor A)) ∧
    (∀ (B : Sheaf J (Type u)) (b : B ⟶ A),
      Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A)) := by
  let := (fibreFullyFaithful A).faithful
  let := (fibreFullyFaithful A).full
  let := fibre_essSurj A
  let : (fibreFunctor A).IsEquivalence := {}
  refine ⟨projection_topology A, projection_cocontinuous A, ?_,
    fun B b ↦ elementMap_continuous b⟩
  exact ⟨(fibreFunctor A).asEquivalence.symm, ⟨Iso.refl _⟩⟩

end CategoryTheory
end
