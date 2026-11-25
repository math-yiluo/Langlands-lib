/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-!
# Existence of the Frobenius of a scheme over a finite field

The `p ^ n`-power absolute Frobenius `AlgebraicGeometry.Scheme.iterateFrobenius` of a scheme in
which the prime `p` vanishes is the `p ^ n`-power Frobenius in the sense of
`AlgebraicGeometry.Scheme.Hom.IsFrobenius` (`AlgebraicGeometry.Scheme.isFrobenius_iterateFrobenius`,
in `WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural`). Consequently every scheme over a
finite field `k` has a `#k`-power Frobenius
(`AlgebraicGeometry.Scheme.Hom.exists_isFrobenius`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every scheme over a finite field `k` has a `#k`-power Frobenius. -/
theorem Hom.exists_isFrobenius {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ∃ F : X ⟶ X, F.IsFrobenius (Nat.card k) := by
  have := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have hX : ((ringChar k : ℕ) : Γ(X, ⊤)) = 0 := by
    rw [← map_natCast ((ΓSpecIso (.of k)).inv ≫ f.appTop).hom, ringChar.Nat.cast_ringChar,
      map_zero]
  refine ⟨X.iterateFrobenius hp hX n, ?_⟩
  rw [Nat.card_eq_fintype_card, hcard]
  exact isFrobenius_iterateFrobenius hp X hX n

end AlgebraicGeometry.Scheme
