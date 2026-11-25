/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-! # Perfectness of finite-free stupid tails

Source: Stacks Project, Tag 08EG, finite-free tail in the proof of Lemma 36.13.6;
Definition 08C4 (blueprint: lem-sc-finite-free-stupid-tail-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Cutting off a bounded-above finite-free sheaf complex below any integer gives a
perfect derived object. Affineness is unnecessary for this part of the construction.
Source: Stacks Project, Tag 08EG, bounded finite-free tail; Definition 08C4.
(blueprint: lem-sc-finite-free-stupid-tail-perfect).

Proof: The stupid tail is zero below r, and above the supplied upper bound by the
termwise truncation isomorphisms. Its nonzero terms remain finite free. On the top
open, restriction preserves zero objects and finite coproducts of the unit sheaf,
so the restricted complex is strictly perfect with these same bounds. The derived
restriction comparison identifies its derived image with the restricted object.
In degrees below r use the zero-rank free sheaf and zero maps as a retract. This
also proves the assertion for the empty scheme and when r exceeds the upper bound.
-/
theorem finiteFree_stupidTail_isPerfect
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (K.X i))
    (hfree : ∀ i : ℤ, ∃ m : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m))))
    (r : ℤ) :
    IsPerfect X (DerivedCategory.Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntGE r))) := by
  classical
  obtain ⟨b, hb⟩ := hbounded
  let T := K.stupidTrunc (ComplexShape.embeddingUpIntGE r)
  have hlow (i : ℤ) (hi : i < r) : IsZero (T.X i) :=
    K.isZero_stupidTrunc_X _ i
      ((ComplexShape.notMem_range_embeddingUpIntGE_iff r i).mpr hi)
  have hhigh (i : ℤ) (hi : b < i) : IsZero (T.X i) := by
    by_cases hir : i < r
    · exact hlow i hir
    · have he : (ComplexShape.embeddingUpIntGE r).f (i - r).toNat = i := by
        change r + ((i - r).toNat : ℤ) = i
        omega
      exact (hb i hi).of_iso (K.stupidTruncXIso _ he)
  intro x
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
  refine ⟨⊤, trivial, (R.mapHomologicalComplex (.up ℤ)).obj T, ?_,
    ⟨R.mapDerivedCategoryFactors.app T⟩⟩
  refine ⟨⟨r, b, ?_⟩, ?_⟩
  · intro i hi
    exact R.map_isZero (hi.elim (hlow i) (hhigh i))
  · intro i
    change ∃ m : ℕ, ∃ (ι : R.obj (T.X i) ⟶ _)
      (π : _ ⟶ R.obj (T.X i)), ι ≫ π = 𝟙 _
    by_cases hi : i < r
    · exact ⟨0, 0, 0, (R.map_isZero (hlow i hi)).eq_of_src _ _⟩
    · have he : (ComplexShape.embeddingUpIntGE r).f (i - r).toNat = i := by
        change r + ((i - r).toNat : ℤ) = i
        omega
      obtain ⟨m, ⟨e⟩⟩ := hfree i
      let e' := R.mapIso (K.stupidTruncXIso _ he ≪≫ e) ≪≫
        (SheafOfModules.mapFreeIso R (ULift.{u} (Fin m)) (Iso.refl _)).symm
      exact ⟨m, e'.hom, e'.inv, e'.hom_inv_id⟩

end AlgebraicGeometry.Scheme
