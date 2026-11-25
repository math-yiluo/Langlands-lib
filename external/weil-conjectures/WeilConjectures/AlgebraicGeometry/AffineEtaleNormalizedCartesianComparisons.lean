/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite

/-!
# Normalized comparison isomorphisms of cartesian affine étale functors

Source: Stacks Project, Étale Cohomology 0EYL, including its coherence discussion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private def underlyingAffineEtale (S : Scheme.{u}) :
    S.FullAffineEtale ⥤ Scheme.{u} :=
  fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S

private theorem compare_cartesian {C : Type*} [Category C] {S T : Scheme.{u}}
    (F G : C ⥤ S.FullAffineEtale) (H : C ⥤ Scheme.{u})
    (r : F ⋙ underlyingAffineEtale S ⟶ H) (t : G ⋙ underlyingAffineEtale S ⟶ H)
    (f : ∀ A, H.obj A ⟶ T) (g : S ⟶ T)
    (hr : ∀ A, IsPullback (r.app A) (F.obj A).obj.hom (f A) g)
    (ht : ∀ A, IsPullback (t.app A) (G.obj A).obj.hom (f A) g) :
    ∃ e : F ≅ G, ∀ A, (e.hom.app A).hom.left ≫ t.app A = r.app A := by
  let e (A : C) : F.obj A ≅ G.obj A :=
    ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk
      ((hr A).isoIsPullback _ _ (ht A))
      ((hr A).isoIsPullback_hom_snd _ _ (ht A)))
  have he (A : C) : (e A).hom.hom.left ≫ t.app A = r.app A :=
    (hr A).isoIsPullback_hom_fst _ _ (ht A)
  refine ⟨NatIso.ofComponents e (fun {A B} a ↦ ?_), he⟩
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Over.Hom.ext
  apply (ht B).hom_ext
  · change (F.map a).hom.left ≫ (e B).hom.hom.left ≫ t.app B =
      (e A).hom.hom.left ≫ (G.map a).hom.left ≫ t.app B
    rw [he B]
    have h₁ := r.naturality a
    have h₂ := t.naturality a
    change (F.map a).hom.left ≫ r.app B = r.app A ≫ H.map a at h₁
    change (G.map a).hom.left ≫ t.app B = t.app A ≫ H.map a at h₂
    rw [h₂, ← Category.assoc, he A, h₁]
  · change ((F.map a) ≫ (e B).hom).hom.left ≫ (G.obj B).obj.hom =
      ((e A).hom ≫ G.map a).hom.left ≫ (G.obj B).obj.hom
    exact ((F.map a) ≫ (e B).hom).hom.w.trans
      (((e A).hom ≫ G.map a).hom.w.symm)

private theorem diagonal_projection {C : Type*} [Category C]
    (F : C ⥤ C) (H : C ⥤ Scheme.{u}) (p : F ⋙ H ⟶ H)
    (hF : F = 𝟭 C) (hp : ∀ A, HEq (p.app A) (𝟙 (H.obj A))) :
    HEq p (𝟙 H) := by
  cases hF
  apply heq_of_eq
  ext A
  exact eq_of_heq (hp A)

private theorem left_diagonal {C B : Type*} [Category C] [Category B]
    (F : C ⥤ C) (G : C ⥤ B) (H : C ⥤ Scheme.{u}) (K : B ⥤ Scheme.{u})
    (p : F ⋙ H ⟶ H) (q : G ⋙ K ⟶ H) (hF : F = 𝟭 C) (hp : HEq p (𝟙 H)) :
    HEq (Functor.whiskerLeft F q ≫ p) q := by
  cases hF
  have hp' : p = 𝟙 H := eq_of_heq hp
  subst p
  apply heq_of_eq
  ext A
  simp

private theorem right_diagonal {C B : Type*} [Category C] [Category B]
    (F : C ⥤ B) (G : B ⥤ B) (H : C ⥤ Scheme.{u}) (K : B ⥤ Scheme.{u})
    (p : F ⋙ K ⟶ H) (q : G ⋙ K ⟶ K) (hG : G = 𝟭 B) (hq : HEq q (𝟙 K)) :
    HEq (Functor.whiskerLeft F q ≫ p) p := by
  cases hG
  have hq' : q = 𝟙 K := eq_of_heq hq
  subst q
  apply heq_of_eq
  ext A
  simp

private theorem comparison_refl {C : Type*} [Category C] {S T : Scheme.{u}}
    {F G : C ⥤ S.FullAffineEtale} (e : F ≅ G) (H : C ⥤ Scheme.{u})
    (r : F ⋙ underlyingAffineEtale S ⟶ H) (t : G ⋙ underlyingAffineEtale S ⟶ H)
    (f : ∀ A, H.obj A ⟶ T) (g : S ⟶ T)
    (ht : ∀ A, IsPullback (t.app A) (G.obj A).obj.hom (f A) g)
    (he : ∀ A, (e.hom.app A).hom.left ≫ t.app A = r.app A)
    (hFG : F = G) (hrt : HEq r t) : HEq e (Iso.refl G) := by
  cases hFG
  have hrt' : r = t := eq_of_heq hrt
  subst r
  apply heq_of_eq
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Over.Hom.ext
  apply (ht A).hom_ext
  · change (e.hom.app A).hom.left ≫ t.app A = (𝟙 _) ≫ t.app A
    simpa only [Category.id_comp] using he A
  · change (e.hom.app A).hom.left ≫ (F.obj A).obj.hom =
      (𝟙 _) ≫ (F.obj A).obj.hom
    simp

/-- Source: Stacks Project, Étale Cohomology 0EYL, its base-change construction and
coherence discussion following the proof.

Proof: The supplied cartesian squares determine the objects of U and v up to the
unique isomorphism respecting their first and structure projections. For i ≤ j ≤ k,
paste the two U object squares. Functoriality of D identifies the composite base arrow
with D.map (homOfLE (h.trans h')).op. Compare this pullback with the supplied single
U_ik pullback using its universal property. The resulting component isomorphisms form
gamma: after composing with the first projection, naturality is exactly naturality of
p; after composing with the structure projection it follows because the arrows are
morphisms over D_k. Pullback uniqueness therefore proves naturality. The first-projection
equation is the defining equation of this comparison. For delta use the identical
construction, pasting the U square with the v square; cone naturality identifies the
composite base arrow with c.π.app (op i).

When i = j or j = k, rewrite U_ii by hid. The supplied hpd makes its first projection
identity. The corresponding functor unitor has identity components and satisfies the
same first- and structure-projection equations as the constructed comparison. Pullback
uniqueness makes the comparisons equal to these unitors. The unitors are heterogeneously
equal to Iso.refl after the identity-composition equalities, giving all three HEq clauses.
No cocycle or site property is asserted.
(blueprint: lem-weil-pbc-affine-etale-normalized-cartesian-comparisons). -/
theorem exists_affineEtale_normalized_cartesian_comparisons
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
    (hid : ∀ i : I, U i i le_rfl = 𝟭 _)
    (hpd : ∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
      HEq ((p i i le_rfl).app A) (𝟙 A.obj.left))
    (hp : ∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
      IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
        A.obj.hom (D.map (homOfLE h).op))
    (hq : ∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
      IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))) :
    ∃ (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i),
      (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
      ∧ (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((gamma i j k h h').hom.app A).hom.left ≫ (p i k (h.trans h')).app A =
          (p j k h').app ((U i j h).obj A) ≫ (p i j h).app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A =
          (q j).app ((U i j h).obj A) ≫ (p i j h).app A) := by
  classical
  let H (i : I) := underlyingAffineEtale (D.obj (op i))
  let r (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
      (U i j h ⋙ U j k h') ⋙ H k ⟶ H i :=
    Functor.whiskerLeft (U i j h) (p j k h') ≫ p i j h
  have hr (i j k : I) (h : i ≤ j) (h' : j ≤ k)
      (A : (D.obj (op i)).FullAffineEtale) :
      IsPullback ((r i j k h h').app A) ((U j k h').obj ((U i j h).obj A)).obj.hom
        A.obj.hom (D.map (homOfLE (h.trans h')).op) := by
    have hb := (hp j k h' ((U i j h).obj A)).paste_horiz (hp i j h A)
    have hm : (homOfLE h').op ≫ (homOfLE h).op =
        (homOfLE (h.trans h')).op := Subsingleton.elim _ _
    simpa only [r, NatTrans.comp_app, Functor.whiskerLeft_app, ← D.map_comp, hm] using hb
  choose gamma hgamma using fun (i j k : I) (h : i ≤ j) (h' : j ≤ k) ↦
    compare_cartesian (U i j h ⋙ U j k h') (U i k (h.trans h')) (H i)
      (r i j k h h') (p i k (h.trans h')) (fun A ↦ A.obj.hom)
      (D.map (homOfLE (h.trans h')).op) (hr i j k h h') (hp i k (h.trans h'))
  let s (i j : I) (h : i ≤ j) : (U i j h ⋙ v j) ⋙ underlyingAffineEtale c.pt ⟶ H i :=
    Functor.whiskerLeft (U i j h) (q j) ≫ p i j h
  have hs (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) :
      IsPullback ((s i j h).app A) ((v j).obj ((U i j h).obj A)).obj.hom
        A.obj.hom (c.π.app (op i)) := by
    have hb := (hq j ((U i j h).obj A)).paste_horiz (hp i j h A)
    have hc : c.π.app (op j) ≫ D.map (homOfLE h).op = c.π.app (op i) :=
      c.w (homOfLE h).op
    simpa only [s, NatTrans.comp_app, Functor.whiskerLeft_app, hc] using hb
  choose delta hdelta using fun (i j : I) (h : i ≤ j) ↦
    compare_cartesian (U i j h ⋙ v j) (v i) (H i) (s i j h) (q i)
      (fun A ↦ A.obj.hom) (c.π.app (op i)) (hs i j h) (hq i)
  have hd (i : I) : HEq (p i i le_rfl) (𝟙 (H i)) :=
    diagonal_projection (U i i le_rfl) (H i) (p i i le_rfl) (hid i) (hpd i)
  refine ⟨gamma, delta, ?_, ?_, ?_, hgamma, hdelta⟩
  · intro i k h
    apply comparison_refl (gamma i i k le_rfl h) (H i)
      (r i i k le_rfl h) (p i k h) (fun A ↦ A.obj.hom)
      (D.map (homOfLE h).op) (hp i k h) (hgamma i i k le_rfl h)
    · rw [hid i]
      rfl
    · exact left_diagonal (U i i le_rfl) (U i k h) (H i) (H k)
        (p i i le_rfl) (p i k h) (hid i) (hd i)
  · intro i k h
    apply comparison_refl (gamma i k k h le_rfl) (H i)
      (r i k k h le_rfl) (p i k h) (fun A ↦ A.obj.hom)
      (D.map (homOfLE h).op) (hp i k h) (hgamma i k k h le_rfl)
    · rw [hid k]
      rfl
    · exact right_diagonal (U i k h) (U k k le_rfl) (H i) (H k)
        (p i k h) (p k k le_rfl) (hid k) (hd k)
  · intro i
    apply comparison_refl (delta i i le_rfl) (H i) (s i i le_rfl) (q i)
      (fun A ↦ A.obj.hom) (c.π.app (op i)) (hq i) (hdelta i i le_rfl)
    · rw [hid i]
      rfl
    · exact left_diagonal (U i i le_rfl) (v i) (H i) (underlyingAffineEtale c.pt)
        (p i i le_rfl) (q i) (hid i) (hd i)

end AlgebraicGeometry.Scheme
