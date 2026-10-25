import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Exponents.Chambers

/-! A finite-coordinate closed-cone criterion for coarse-block stabilizers. -/

namespace Langlands.Exponents

open GeneralLinear Geometric
open scoped BigOperators

/-- A shifted-parameter stabilizer preserves the coarse blocks if its unshifted
vector lies in the closed positive root cone after permutation. -/
def ClosedConeStabilizerRigidityStatement : Prop :=
  ∀ (n : ℕ) (B : BlockShape n) (v : Fin n → ℝ)
    (t : Fin B.length → ℝ) (w : Equiv.Perm (Fin n)),
    (∀ i : Fin B.length, ∑ a : Fin (B.size i), v (B.index i a) = 0) →
    StrictAnti t →
    IsClosedPositiveRootCone (fun a => v (w a)) →
    (∀ a : Fin n,
      v (w a) - t (blockIndex B (w a)) = v a - t (blockIndex B a)) →
      w ∈ blockWeyl B ∧ ∀ a : Fin n, v (w a) = v a

end Langlands.Exponents
