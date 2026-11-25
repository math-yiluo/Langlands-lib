/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The negation on the second factor of a product of affine spaces

The automorphism `(x, y) ↦ (-x, y)` of `𝔸ⁿ_S ×_S 𝔸ⁿ_S` (`AlgebraicGeometry.Etale.negProd`) and its
effect on the standard pairing.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

section NegProd

variable (n : Type u) (S : Scheme.{u})

/-- The automorphism `ι × 1 : (x, ξ) ↦ (-x, ξ)` of `𝔸(n; S) ×_S 𝔸(n; S)`. -/
noncomputable def negProd : pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ⟶
    pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
  pullback.map _ _ _ _ (neg n S) (𝟙 _) (𝟙 S) (by simp [neg_over]) (by simp)

@[reassoc (attr := simp)]
lemma negProd_fst : negProd n S ≫ pullback.fst _ _ = pullback.fst _ _ ≫ neg n S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma negProd_snd : negProd n S ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma negProd_negProd : negProd n S ≫ negProd n S = 𝟙 _ := by
  ext <;> simp [AffineSpace.neg_comp_neg]

instance : IsIso (negProd n S) := ⟨negProd n S, negProd_negProd n S, negProd_negProd n S⟩

lemma negProd_appTop_stdPairing [Fintype n] :
    (negProd n S).appTop (stdPairing n S) = -stdPairing n S := by
  simp only [stdPairing, map_sum, map_mul, ← neg_mul, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, negProd_fst, negProd_snd, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, neg_appTop_coord, map_neg]

end NegProd

end AlgebraicGeometry.Etale
