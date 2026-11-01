import Langlands.Representation.Exponents.Chambers

/-! # Complementary prefixes cannot both satisfy the strict cone inequalities -/

namespace Langlands.Exponents

/-- A nonempty proper finite subset and its entire complement cannot both be
positive prefixes of permutations of the same total-zero vector. -/
def ComplementaryPrefixConeObstructionStatement : Prop :=
  ∀ {r : ℕ} (x : Fin r → ℝ) (S : Finset (Fin r))
    (e f : Equiv.Perm (Fin r)),
    S.Nonempty → Sᶜ.Nonempty →
    (∀ i : Fin r, (i : ℕ) < S.card ↔ e i ∈ S) →
    (∀ i : Fin r, (i : ℕ) < Sᶜ.card ↔ f i ∈ Sᶜ) →
    IsPositiveRootCone (x ∘ e) →
    IsPositiveRootCone (x ∘ f) → False

end Langlands.Exponents
