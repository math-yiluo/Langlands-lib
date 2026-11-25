/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionConstruction
import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionSplit
import Mathlib.Basic.Finite.Sum

/-! # Finite attachment to a split truncated simplicial family

Source: Stacks Project, Tags 0DAV and 0DAU
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

private theorem index_surjective {A B : FormalCoproduct.{w} D} (h : A = B) :
    Function.Surjective (eqToHom h).f := by
  subst B
  exact Function.surjective_id

/-- Attach a finite family along its prescribed boundary.
Source: Stacks 0DAV, construction of the extension, and 0DAU, split convention
(auxiliary; not a blueprint node).

Proof: Compose v with the matching projections to obtain a compatible boundary
cone on V. Normalize each old index using the split bijection and its component
isomorphism. Attach the new family in degree n+1; for an arbitrary ordinal map,
use its epi--mono image factorization, an old operator or the prescribed face
cone, and inverse normalization. The factorization identities prove composition
in all eight old/top cases. This constructs the extended functor with its
prescribed faces and normalized degeneracies. These degeneracies show that the
old labels give exactly the degenerate indices in the new degree, and have
invertible components; old degrees inherit splitness by restriction. The matching
universal property gives b, and its uniqueness gives the prescribed restriction
v. Finite old indices and the finiteness of ordinal maps give finite label sets,
hence finiteness in the new degree. The old summand face formula is the explicit
face construction.
-/
theorem exists_split_truncated_extension
    [HasFiniteLimits D]
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (hfinite : ∀ q : Fin (n + 1), Finite (term K q).I) (hsplit : IsSplit K)
    {M : FormalCoproduct.{w} D} (c : BoundaryCone K M) (hc : IsMatching K c)
    (V : FormalCoproduct.{w} D) [Finite V.I] (v : V ⟶ M) :
    ∃ (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
      (e : (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D)
        (n + 1) n (Nat.le_succ n)).obj L = K)
      (t : attachedFamily K V = term L ⟨n + 1, Nat.lt_succ_self _⟩)
      (b : term L ⟨n + 1, Nat.lt_succ_self _⟩ ⟶ M),
      IsSplit L ∧
      (∀ q : Fin (n + 2), Finite (term L q).I) ∧
      (∀ x : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I,
        IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ x ↔
          ∃ j : V.I, (eqToHom t).f (Sum.inl j) = x) ∧
      (∀ (q : Fin (n + 1))
        (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
        b ≫ c.projection q α =
          operator L (q := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩)
            (r := ⟨n + 1, Nat.lt_succ_self _⟩) α ≫ (eqToHom e).app (op (degree q))) ∧
      (newInclusion K V ≫ eqToHom t ≫ b = v) ∧
      (∀ (a : Labels K (n + 1)) (i : Fin (n + 2)),
        oldInclusion K V a ≫ eqToHom t ≫
          operator L (q := ⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩)
            (r := ⟨n + 1, Nat.lt_succ_self _⟩) (SimplexCategory.δ i) ≫
            (eqToHom e).app (op (degree ⟨n, Nat.lt_succ_self _⟩)) =
          FormalCoproduct.Hom.fromIncl a.2.2.val (𝟙 _) ≫
            operator K (q := ⟨n, Nat.lt_succ_self _⟩)
              (SimplexCategory.δ i ≫ a.2.1.val)) := by
  let p : BoundaryCone K V :=
    { projection := fun q α ↦ v ≫ c.projection q α
      naturality := by
        intro q r α β
        rw [Category.assoc, c.naturality] }
  obtain ⟨L, e, t, hnew, hold, hd, hφ⟩ := exists_attachment_operators K hsplit V p
  obtain ⟨hsL, hnd⟩ := split_attachment_of_degeneracies K hsplit V L e t hd hφ
  let d : BoundaryCone K (term L ⟨n + 1, Nat.lt_succ_self _⟩) :=
    { projection := fun q α ↦
        operator L (q := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩)
          (r := ⟨n + 1, Nat.lt_succ_self _⟩) α ≫ (eqToHom e).app (op (degree q))
      naturality := by
        intro q r α β
        subst K
        change (L.map _ ≫ 𝟙 _) ≫ L.map _ = L.map _ ≫ 𝟙 _
        rw [Category.comp_id, Category.comp_id, ← L.map_comp]
        rfl }
  obtain ⟨b, hb, huniq⟩ := hc _ d
  have hv : newInclusion K V ≫ eqToHom t ≫ b = v := by
    apply (hc V p).unique
    · intro q α
      rw [Category.assoc, Category.assoc, hb]
      exact hnew q α
    · intro q α
      rfl
  have hfL : ∀ q : Fin (n + 2), Finite (term L q).I := by
    intro q
    by_cases hq : q.val < n + 1
    · let r : Fin (n + 1) := ⟨q.val, hq⟩
      have : Finite (term K r).I := hfinite r
      have he : term L q = term K r := by
        subst K
        rfl
      rw [he]
      infer_instance
    · have hqb := q.isLt
      have heq : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst q
      have : Finite (Labels K (n + 1)) := finite_labels K hfinite (n + 1)
      have : Finite (attachedFamily K V).I := inferInstanceAs (Finite (V.I ⊕ Labels K _))
      exact Finite.of_surjective _ (index_surjective t)
  refine ⟨L, e, t, b, hsL, hfL, hnd, hb, hv, ?_⟩
  intro a i
  exact hold a ⟨n, Nat.lt_succ_self _⟩ (SimplexCategory.δ i)

end CategoryTheory.FormalSplitAttachment
