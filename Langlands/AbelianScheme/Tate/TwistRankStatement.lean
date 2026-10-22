import Langlands.AbelianScheme.Tate.Twist
import Mathlib.FieldTheory.IsSepClosed

namespace Langlands.TateTwist

universe u

/-- The actual integral Tate twist over a separably closed field, away from its
characteristic, is a free module of rank one. This is a proposition to prove. -/
def IntegralRankOne (Ω : Type u) [Field Ω] (p : ℕ) [Fact p.Prime] : Prop :=
  IsSepClosed Ω → (p : Ω) ≠ 0 →
    Nonempty (ℤ_[p] ≃ₗ[ℤ_[p]] Integral Ω p)

end Langlands.TateTwist
