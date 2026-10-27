import Langlands.Group.GL.CartanQuotientDefinitions

/-!
# Counting left cosets in an antidominant Cartan double coset

For the standard integral subgroup `K` of `GL_n(F)` and the diagonal
representative `a(lam)` of an antitone exponent tuple, the double coset
`K a(lam) K` is covered by a finite family of left translates `r a(lam) K`
whose number is at most a constant multiple of `delta(lam)⁻¹`.
-/

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

/-- For every rank there is a constant `c` such that, for every antitone exponent
tuple `lam`, some finite set `R` of at most `c * (delta T lam)⁻¹` elements satisfies
`K a(lam) K ⊆ ⋃_{r ∈ R} r a(lam) K`, where `K` is the standard integral subgroup. -/
def CartanCellCountStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
    ∃ c : ℝ, ∀ lam : Fin n → ℤ, Antitone lam →
      ∃ R : Finset (GeneralLinear n F.Carrier),
        (R.card : ℝ) ≤ c * (delta T lam)⁻¹ ∧
        ∀ k₁ ∈ maximalCompact T n, ∀ k₂ ∈ maximalCompact T n,
          ∃ r ∈ R, ∃ k ∈ maximalCompact T n,
            k₁ * representative T lam * k₂ = r * representative T lam * k

end Langlands.GeneralLinear.CartanQuotient
