/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentComposition

/-! # Operators for one split simplicial attachment

Source: Stacks Project, Tag 0DAV (lemma-hypercovering-object), construction of the
extension and the final simplicial composition check; Tag 0DAU (lemma-split).
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

/-- Realize the prescribed lower faces and normalized top degeneracies as a functor.
Source: Stacks Project, Tag 0DAV, construction of the extension, with the composition
verification expanded in the parent node's steps 3 and 4.
(auxiliary; not a blueprint node).

Proof: Normalize every old index by the split bijection, with component isomorphism
`e_(σ,i)`. Use the prescribed cone on new summands and the old operators on old
summands for proper injective operators. For an arbitrary ordinal operator, factor
its composite with the source label as an epimorphism followed by a monomorphism.
Apply the proper-face operator, normalize its output, and concatenate the remaining
epimorphism with that label. Its component is the face component followed by the
inverse of the output normalization isomorphism. The only full-image case in degree
`n+1` is the identity, where use the identity on the new summand.
For composition, factor the next operator through the image of the first one.
Both routes then have the same concatenated epimorphism, and functoriality in the
old truncation cancels the intermediate normalization isomorphism. Naturality of
`p` gives the same identity on a new summand. Transport to the original old families.
The new-face and old-face equations are the definitions of these operators. An epi
only concatenates a label; its component is an inverse old normalization isomorphism,
so is invertible. Empty families and dimension zero use the identical formulas. -/
theorem exists_attachment_operators
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) :
    ∃ (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
      (e : (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D)
        (n + 1) n (Nat.le_succ n)).obj L = K)
      (t : attachedFamily K V = term L ⟨n + 1, Nat.lt_succ_self _⟩),
      (∀ (q : Fin (n + 1))
        (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
        newInclusion K V ≫ eqToHom t ≫
          operator L (q := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩)
            (r := ⟨n + 1, Nat.lt_succ_self _⟩) α ≫
              (eqToHom e).app (op (degree q)) = p.projection q α) ∧
      (∀ (a : Labels K (n + 1)) (q : Fin (n + 1))
        (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
        oldInclusion K V a ≫ eqToHom t ≫
          operator L (q := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩)
            (r := ⟨n + 1, Nat.lt_succ_self _⟩) α ≫
              (eqToHom e).app (op (degree q)) =
          FormalCoproduct.Hom.fromIncl a.2.2.val (𝟙 _) ≫ operator K (α ≫ a.2.1.val)) ∧
      (∀ (q : Fin (n + 1))
        (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ)
        (i : (term L ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩).I),
        (operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
          (r := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩) σ).f i = (eqToHom t).f (Sum.inr
          (precomposeLabel K
            (normalization K hs q (((eqToHom e).app (op (degree q))).f i)) σ hσ))) ∧
      (∀ (q : Fin (n + 1))
        (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (_ : Epi σ)
        (i : (term L ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩).I),
        IsIso ((operator L (q := ⟨n + 1, Nat.lt_succ_self _⟩)
          (r := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩) σ).φ i)) := by
  let L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1) :=
    { obj := fun X ↦ attachmentTerm K V ⟨X.unop.obj.len, Nat.lt_succ_of_le X.unop.property⟩
      map := fun {X Y} f ↦ attachmentMap K hs V p
        ⟨Y.unop.obj.len, Nat.lt_succ_of_le Y.unop.property⟩
        ⟨X.unop.obj.len, Nat.lt_succ_of_le X.unop.property⟩ f.unop.hom
      map_id := fun X ↦ attachmentMap_id K hs V p _
      map_comp := by
        intro X Y Z f g
        exact attachmentMap_comp K hs V p
          ⟨Z.unop.obj.len, Nat.lt_succ_of_le Z.unop.property⟩
          ⟨Y.unop.obj.len, Nat.lt_succ_of_le Y.unop.property⟩
          ⟨X.unop.obj.len, Nat.lt_succ_of_le X.unop.property⟩ g.unop.hom f.unop.hom }
  have e : (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D)
      (n + 1) n (Nat.le_succ n)).obj L = K := by
    apply CategoryTheory.Functor.hext
    · intro X
      simp [L, attachmentTerm, term, degree, Nat.lt_succ_of_le X.unop.property]
    · intro X Y f
      simp [L, attachmentMap, attachmentTerm, term, degree, operator,
        Nat.lt_succ_of_le X.unop.property, Nat.lt_succ_of_le Y.unop.property]
      rfl
  have t : attachedFamily K V = term L ⟨n + 1, Nat.lt_succ_self _⟩ := by
    simp [L, term, degree, attachmentTerm]
  refine ⟨L, e, t, ?_, ?_, ?_, ?_⟩
  · intro q α
    suffices h : newInclusion K V ≫ attachFace K V p q α = p.projection q α by
      simpa [operator, L, attachmentMap, term, degree, attachmentTerm, q.isLt,
        eqToHom_app] using h
    refine FormalCoproduct.hom_ext rfl ?_
    intro j
    simp [newInclusion, attachFace]
  · intro a q α
    suffices h : oldInclusion K V a ≫ attachFace K V p q α =
        FormalCoproduct.Hom.fromIncl a.2.2.val (𝟙 _) ≫ operator K (α ≫ a.2.1.val) by
      simpa [operator, L, attachmentMap, term, degree, attachmentTerm, q.isLt,
        eqToHom_app] using h
    refine FormalCoproduct.hom_ext rfl ?_
    intro j
    simp [oldInclusion, attachFace, FormalCoproduct.Hom.fromIncl]
  · intro q σ hσ i
    simp [operator, L, attachmentMap, term, degree, attachmentTerm, q.isLt,
      eqToHom_app, attachLift_epi K hs V q σ hσ, attachEpi]
  · intro q σ hσ i
    exact attachmentMap_epi_component_iso K hs V p q σ hσ i

end CategoryTheory.FormalSplitAttachment
