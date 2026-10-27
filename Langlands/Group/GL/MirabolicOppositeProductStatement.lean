import Langlands.Group.GL.MirabolicOppositeIntersection

/-!
# The actual opposite-parabolic–mirabolic product

An internal algebraic statement identifying actual factors with an inverse-row
coordinate condition. This module supplies no proof.
-/

namespace Langlands.GeneralLinear

universe u

/-- A matrix is an opposite-parabolic factor followed by a mirabolic factor
exactly when its inverse last row has a nonzero tail coordinate. -/
def MirabolicOppositeProductStatement : Prop :=
  ∀ (K : Type u) [Field K] (a b : ℕ) (ha : 0 < a)
    (g : GeneralLinear (a + b + 1) K),
    (∃ (r : (MirabolicOppositeIntersection.shape a b ha).oppositeParabolic K)
       (m : mirabolic (a + b) K),
      g = r.val * m.val) ↔
    ∃ j : Fin (b + 1),
      (g⁻¹) (Fin.last (a + b)) (Fin.natAdd a j) ≠ 0

end Langlands.GeneralLinear
