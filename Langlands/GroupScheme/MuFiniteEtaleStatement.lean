import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite étaleness of the actual roots-of-unity group scheme -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual roots-of-unity group scheme is finite étale over any base scheme
when its positive index is invertible in the global section ring.
This proposition is a statement target, not a proof. -/
def MuFiniteEtaleStatement : Prop :=
  ∀ (S : Scheme.{u}) (n : ℕ),
    0 < n → IsUnit (n : Γ(S, ⊤)) →
      IsFinite (mu S n).X.hom ∧ Etale (mu S n).X.hom

end Langlands.GroupScheme
