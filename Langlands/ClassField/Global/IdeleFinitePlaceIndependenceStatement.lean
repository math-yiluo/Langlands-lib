import Langlands.ClassField.Global.IdeleFiniteInvariantTransfer

/-! # Finite idele invariant independence from the upper place -/

namespace Langlands.ClassField.Global

open Langlands.ClassFieldTheory.Local

universe u

/-- Local inflation compatibility implies independence from the chosen upper finite place. -/
def FiniteIdeleInvariantPlaceIndependenceStatement : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility) →
      FiniteIdeleInvariantPlaceIndependent I

end Langlands.ClassField.Global
