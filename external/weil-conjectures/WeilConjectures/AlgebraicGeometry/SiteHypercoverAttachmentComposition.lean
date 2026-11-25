/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentOperators

/-! # Composition of explicit attachment operators

Source: Stacks Project, Tag 0DAV (lemma-hypercovering-object), construction of the
extension and the final simplicial composition check; Tag 0DAU (lemma-split).
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

private theorem transport_attachment_equality
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (q s : Fin (n + 2))
    {A B : FormalCoproduct.{w} D} (hs : attachmentTerm K V s = A)
    (hq : attachmentTerm K V q = B) {f g : A ⟶ B} (h : f = g) :
    eqToHom hs ≫ f ≫ eqToHom hq.symm =
      eqToHom hs ≫ g ≫ eqToHom hq.symm := by rw [h]

/-- The explicitly constructed attachment operators compose contravariantly.
Source: Stacks Project, Tag 0DAV, final paragraph of lemma-hypercovering-object;
expanded by steps 3 and 4 of lem-weil-pbc-site-hypercover-finite-extension.
(auxiliary; not a blueprint node).

Proof: Work in normalized coordinates in the old degrees. An old summand has label
`(r,σ,i)` and normalization component `e_(σ,i)`. Factor the composite of an ordinal
operator and `σ` uniquely into its image epimorphism `ρ` and inclusion `τ`. On a new
summand use the prescribed compatible cone `p` for the proper image inclusion; on
an old summand use the old functor. Normalize the resulting old index and compose
its label with `ρ`. This describes `attachmentMap` in all four old/top cases.
For two successive operators, factor the second one through the image of the first.
Both routes have the same image inclusion and concatenated epimorphism. Functoriality
of `K`, or naturality of `p` on a new summand, identifies their unnormalized maps.
The intervening component isomorphism and its inverse cancel, and the bijectivity
of old label normalization identifies their indices. The full-image top case is the
identity endomorphism and requires no factorization. Morphism extensionality of
formal coproducts then proves the equality. This works without finite limits,
finiteness assumptions, or a matching universal property. -/
theorem attachmentMap_comp
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V)
    (q r s : Fin (n + 2))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk s.val) :
    attachmentMap K hs V p q s (α ≫ β) =
      attachmentMap K hs V p r s β ≫ attachmentMap K hs V p q r α := by
  classical
  have htop (a : Fin (n + 2)) (ha : ¬ a.val < n + 1) :
      a = ⟨n + 1, Nat.lt_succ_self _⟩ := by
    have hb := a.isLt
    exact Fin.ext (by dsimp; omega)
  by_cases hq : q.val < n + 1
  · by_cases hr : r.val < n + 1
    · by_cases hss : s.val < n + 1
      · have hc : operator K (q := ⟨q.val, hq⟩) (r := ⟨s.val, hss⟩) (α ≫ β) =
            operator K (q := ⟨r.val, hr⟩) (r := ⟨s.val, hss⟩) β ≫
              operator K (q := ⟨q.val, hq⟩) (r := ⟨r.val, hr⟩) α := by
          dsimp [operator]
          rw [← K.map_comp]
          rfl
        simpa [attachmentMap, attachmentTerm, hq, hr, hss, Category.assoc] using
          transport_attachment_equality K V q s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm, hq]) hc
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, hq, hr, Category.assoc] using
          transport_attachment_equality K V q ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm, hq])
            ((attachFace_naturality K V p ⟨q.val, hq⟩ ⟨r.val, hr⟩ α β).symm)
    · have he := htop r hr
      subst r
      by_cases hss : s.val < n + 1
      · simpa [attachmentMap, attachmentTerm, hq, hss, Category.assoc] using
          transport_attachment_equality K V q s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm, hq])
            ((attachLift_face K hs V p ⟨s.val, hss⟩ ⟨q.val, hq⟩ β α).symm)
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, hq, Category.assoc] using
          transport_attachment_equality K V q ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm, hq])
            ((attachEnd_face K hs V p ⟨q.val, hq⟩ β α).symm)
  · have he := htop q hq
    subst q
    by_cases hr : r.val < n + 1
    · by_cases hss : s.val < n + 1
      · simpa [attachmentMap, attachmentTerm, hr, hss, Category.assoc] using
          transport_attachment_equality K V ⟨n + 1, Nat.lt_succ_self _⟩ s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm])
            (attachLift_naturality K hs V ⟨s.val, hss⟩ ⟨r.val, hr⟩ α β)
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, hr, Category.assoc] using
          transport_attachment_equality K V ⟨n + 1, Nat.lt_succ_self _⟩ ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm])
            (attachEnd_lift K hs V p ⟨r.val, hr⟩ α β)
    · have he := htop r hr
      subst r
      by_cases hss : s.val < n + 1
      · simpa [attachmentMap, attachmentTerm, hss, Category.assoc] using
          transport_attachment_equality K V ⟨n + 1, Nat.lt_succ_self _⟩ s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm])
            (attachLift_end K hs V p ⟨s.val, hss⟩ α β)
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, Category.assoc] using
          transport_attachment_equality K V ⟨n + 1, Nat.lt_succ_self _⟩ ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm])
            (attachEnd_comp K hs V p α β)

end CategoryTheory.FormalSplitAttachment
