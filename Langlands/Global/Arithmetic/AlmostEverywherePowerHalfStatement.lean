import Langlands.Global.Adelic

/-!
# Almost-everywhere local powers and global half-powers
-/

universe u

namespace Langlands.Global

/-- The consequence of Artin--Tate IX.1 Theorem 1 needed for unconditional
period doubling: a global unit locally a `(2*n)`th power outside finitely many
finite places is a global `n`th power. -/
def AlmostEverywherePowerHalfStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (n : ℕ), 0 < n → ∀ a : Kˣ,
    (∀ v : FinitePlace K, v ∉ S →
      ∃ b : (FiniteCompletion K v)ˣ,
        b ^ (2 * n) = Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a) →
    ∃ b : Kˣ, b ^ n = a

end Langlands.Global
