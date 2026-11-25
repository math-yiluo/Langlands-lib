/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase

/-! # Splitness of a normalized simplicial attachment

Source: Stacks Project, Tag 0DAU, characterization by invertible degeneracy components,
and Tag 0DAV, the new index set.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

private abbrev restriction (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1)) :=
  (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D) (n + 1) n).obj L

private theorem nondegenerate_restriction
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (q : Fin (n + 1)) (i : (term (restriction L) q).I) :
    IsNondegenerate (restriction L) q i ↔
      IsNondegenerate L ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩ i := by
  unfold IsNondegenerate
  apply not_congr
  constructor
  · rintro ⟨r, hr, σ, hσ, j, hj⟩
    exact ⟨⟨r.val, Nat.lt_succ_of_lt r.isLt⟩, hr, σ, hσ, j, hj⟩
  · rintro ⟨r, hr, σ, hσ, j, hj⟩
    have hr' : r.val < n + 1 := lt_trans hr q.isLt
    exact ⟨⟨r.val, hr'⟩, hr, σ, hσ, j, hj⟩

private def retainedLabel
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (q : ℕ) (a : Labels (restriction L) q) : Labels L q :=
  ⟨⟨a.1.val, Nat.lt_succ_of_lt a.1.isLt⟩,
    a.2.1, ⟨a.2.2.val, (nondegenerate_restriction L a.1 a.2.2.val).mp a.2.2.property⟩⟩

private def restrictedLabel
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (q : Fin (n + 1)) (a : Labels L q.val) : Labels (restriction L) q.val := by
  have := a.2.1.property
  have hr : a.1.val < n + 1 :=
    lt_of_le_of_lt (SimplexCategory.len_le_of_epi a.2.1.val) q.isLt
  exact ⟨⟨a.1.val, hr⟩, a.2.1,
    ⟨a.2.2.val, (nondegenerate_restriction L ⟨a.1.val, hr⟩ a.2.2.val).mpr
      a.2.2.property⟩⟩

private def retainedLabelEquiv
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (q : Fin (n + 1)) : Labels (restriction L) q.val ≃ Labels L q.val where
  toFun := retainedLabel L q.val
  invFun := restrictedLabel L q
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

private theorem split_retained
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (hs : IsSplit (restriction L)) (q : Fin (n + 1)) :
    Function.Bijective (labelIndex L ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩) ∧
      ∀ a : Labels L q.val,
        IsIso ((operator L (q := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩)
          (r := a.1) a.2.1.val).φ a.2.2.val) := by
  constructor
  · have h := (hs.1 q).comp (retainedLabelEquiv L q).symm.bijective
    exact h
  · intro a
    exact hs.2 q (restrictedLabel L q a)

private theorem normalize_nondegenerate
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (q : Fin (n + 1)) (i : (term K q).I) (hi : IsNondegenerate K q i) :
    normalization K hs q i = ⟨q, ⟨⟨𝟙 _, inferInstance⟩, ⟨i, hi⟩⟩⟩ := by
  apply (Equiv.ofBijective (labelIndex K q) (hs.1 q)).injective
  simp only [normalization, Equiv.ofBijective_apply, Equiv.apply_symm_apply,
    labelIndex, operator]
  change i = (K.map (𝟙 _)).f i
  rw [K.map_id]
  rfl

private theorem precompose_normalize_nondegenerate
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (a : Labels K (n + 1)) :
    precomposeLabel K (normalization K hs a.1 a.2.2.val) a.2.1.val a.2.1.property = a := by
  rw [normalize_nondegenerate K hs a.1 a.2.2.val a.2.2.property]
  rcases a with ⟨r, ⟨⟨σ, hσ⟩, ⟨i, hi⟩⟩⟩
  simp [precomposeLabel]

private theorem index_bijective {A B : FormalCoproduct.{w} D} (h : A = B) :
    Function.Bijective (eqToHom h).f := by
  subst B
  exact Function.bijective_id

private def identityLabel
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (i : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I)
    (hi : IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ i) : Labels L (n + 1) :=
  ⟨⟨n + 1, Nat.lt_succ_self _⟩, ⟨⟨𝟙 _, inferInstance⟩, ⟨i, hi⟩⟩⟩

private theorem labelIndex_identity
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (i : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I)
    (hi : IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ i) :
    labelIndex L ⟨n + 1, Nat.lt_succ_self _⟩ (identityLabel L i hi) = i := by
  change (L.map (𝟙 _)).f i = i
  rw [L.map_id]
  rfl

private theorem top_label_cases
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (a : Labels L (n + 1)) :
    (∃ b : Labels (restriction L) (n + 1), retainedLabel L (n + 1) b = a) ∨
      ∃ (i : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I)
        (hi : IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ i),
        identityLabel L i hi = a := by
  rcases a with ⟨r, ⟨⟨σ, hσ⟩, ⟨i, hi⟩⟩⟩
  by_cases hr : r.val < n + 1
  · left
    exact ⟨⟨⟨r.val, hr⟩, ⟨⟨σ, hσ⟩,
      ⟨i, (nondegenerate_restriction L ⟨r.val, hr⟩ i).mpr hi⟩⟩⟩, rfl⟩
  · have hb := r.isLt
    have hr' : r = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
    subst r
    have hσ' : σ = 𝟙 _ := SimplexCategory.eq_id_of_epi σ
    subst σ
    exact Or.inr ⟨i, hi, rfl⟩

/-- The explicit top degeneracies force splitness and identify the new nondegenerates.
Source: Stacks Project, Tags 0DAV and 0DAU.
(auxiliary; not a blueprint node).

Proof: Restriction preserves nondegeneracy in every old degree: any degeneracy
source has smaller degree and hence still belongs to the restriction. The labels
in an old degree are unchanged, since an epimorphism cannot increase dimension.
At the top, each proper degeneracy has an old label as its index. Conversely every
old label is the degeneracy of its underlying nondegenerate old index; normalization
of a nondegenerate index has the identity label. Thus the remaining indices are
exactly the new ones. Old normalized labels map bijectively to the old top summands,
and identity labels on new indices map bijectively to new summands. These images
are disjoint. All proper top component maps are isomorphisms by hypothesis, and
the remaining components are identities. This proves the two split conditions. -/
theorem split_attachment_of_degeneracies
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D)
    (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
    (e : (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D)
      (n + 1) n (Nat.le_succ n)).obj L = K)
    (t : attachedFamily K V = term L ⟨n + 1, Nat.lt_succ_self _⟩)
    (hd : ∀ (q : Fin (n + 1))
      (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ)
      (i : (term L ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩).I),
      (operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
        (r := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩) σ).f i =
        (eqToHom t).f (Sum.inr (precomposeLabel K
          (normalization K hs q (((eqToHom e).app (op (degree q))).f i)) σ hσ)))
    (hφ : ∀ (q : Fin (n + 1))
      (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (_ : Epi σ)
      (i : (term L ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩).I),
      IsIso ((operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
        (r := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩) σ).φ i)) :
    IsSplit L ∧
      ∀ x : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I,
        IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ x ↔
          ∃ j : V.I, (eqToHom t).f (Sum.inl j) = x := by
  subst K
  have ht := index_bijective t
  have hnd : ∀ x : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I,
      IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ x ↔
        ∃ j : V.I, (eqToHom t).f (Sum.inl j) = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := ht.2 x
      cases z with
      | inl j => exact ⟨j, rfl⟩
      | inr a =>
        exfalso
        have ha := hd a.1 a.2.1.val a.2.1.property a.2.2.val
        change (operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
          (r := ⟨a.1.val, Nat.lt_succ_of_lt a.1.isLt⟩) a.2.1.val).f a.2.2.val =
          (eqToHom t).f (Sum.inr
            (precomposeLabel _ (normalization _ hs a.1 a.2.2.val)
              a.2.1.val a.2.1.property)) at ha
        rw [precompose_normalize_nondegenerate] at ha
        exact hx ⟨⟨a.1.val, Nat.lt_succ_of_lt a.1.isLt⟩, a.1.isLt,
          a.2.1.val, a.2.1.property, a.2.2.val, ha⟩
    · rintro ⟨j, rfl⟩ ⟨r, hr, σ, hσ, i, hi⟩
      let q : Fin (n + 1) := ⟨r.val, hr⟩
      have hd' := hd q σ hσ i
      rw [hd'] at hi
      exact Sum.inr_ne_inl (ht.1 hi)
  have hret (a : Labels (restriction L) (n + 1)) :
      labelIndex L ⟨n + 1, Nat.lt_succ_self _⟩ (retainedLabel L (n + 1) a) =
        (eqToHom t).f (Sum.inr a) := by
    have ha := hd a.1 a.2.1.val a.2.1.property a.2.2.val
    change (operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
      (r := ⟨a.1.val, Nat.lt_succ_of_lt a.1.isLt⟩) a.2.1.val).f a.2.2.val =
        (eqToHom t).f (Sum.inr (precomposeLabel _
          (normalization _ hs a.1 a.2.2.val) a.2.1.val a.2.1.property)) at ha
    rw [precompose_normalize_nondegenerate] at ha
    exact ha
  have hbij : Function.Bijective (labelIndex L ⟨n + 1, Nat.lt_succ_self _⟩) := by
    constructor
    · intro a b hab
      rcases top_label_cases L a with ⟨a', rfl⟩ | ⟨i, hi, rfl⟩
      · rcases top_label_cases L b with ⟨b', rfl⟩ | ⟨j, hj, rfl⟩
        · rw [hret, hret] at hab
          have he : a' = b' := Sum.inr.inj (ht.1 hab)
          subst b'
          rfl
        · obtain ⟨k, hk⟩ := (hnd j).mp hj
          rw [hret, labelIndex_identity, ← hk] at hab
          exact (Sum.inr_ne_inl (ht.1 hab)).elim
      · rcases top_label_cases L b with ⟨b', rfl⟩ | ⟨j, hj, rfl⟩
        · obtain ⟨k, hk⟩ := (hnd i).mp hi
          rw [hret, labelIndex_identity, ← hk] at hab
          exact (Sum.inl_ne_inr (ht.1 hab)).elim
        · rw [labelIndex_identity, labelIndex_identity] at hab
          subst j
          rfl
    · intro x
      obtain ⟨z, rfl⟩ := ht.2 x
      cases z with
      | inl j =>
        exact ⟨identityLabel L _ ((hnd _).mpr ⟨j, rfl⟩), labelIndex_identity _ _ _⟩
      | inr a => exact ⟨retainedLabel L (n + 1) a, hret a⟩
  have hiso (a : Labels L (n + 1)) :
      IsIso ((operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
        (r := a.1) a.2.1.val).φ a.2.2.val) := by
    rcases top_label_cases L a with ⟨a, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hφ a.1 a.2.1.val a.2.1.property a.2.2.val
    · change IsIso ((L.map (𝟙 _)).φ i)
      rw [L.map_id]
      change IsIso (𝟙 _)
      infer_instance
  refine ⟨⟨?_, ?_⟩, hnd⟩
  · intro q
    by_cases hq : q.val < n + 1
    · exact (split_retained L hs ⟨q.val, hq⟩).1
    · have hb := q.isLt
      have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst q
      exact hbij
  · intro q a
    by_cases hq : q.val < n + 1
    · exact (split_retained L hs ⟨q.val, hq⟩).2 a
    · have hb := q.isLt
      have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst q
      exact hiso a

end CategoryTheory.FormalSplitAttachment
