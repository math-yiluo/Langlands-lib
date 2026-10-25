import Langlands.ClassField.Global.IdeleFiniteInvariantTransfer

/-! # Finite idele invariant restriction from local relative restriction -/

namespace Langlands.ClassField.Global

open Langlands.ClassFieldTheory.Local

universe u

/-- Local relative restriction implies the actual finite idele restriction law. -/
def FiniteIdeleInvariantRestrictionStatement : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime], (I p).RelativeRestriction) →
      FiniteIdeleInvariantRestriction I

end Langlands.ClassField.Global
