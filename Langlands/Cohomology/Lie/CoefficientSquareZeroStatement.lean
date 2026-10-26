import Langlands.Cohomology.Lie.CoefficientCochains

/-!
# Square-zero target for the coefficient Chevalley–Eilenberg differential

This proposition refers to the constructed coefficient differential.
-/

namespace Langlands.Cohomology.Lie

universe u v w

/-- The constructed coefficient differential squares to zero in every degree. -/
def DifferentialSquareZero (K : Type u) (L : Type v) (M : Type w)
    [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] : Prop :=
  ∀ q : ℕ,
    (differential (K := K) (L := L) (M := M) (q + 1)).comp (differential q) = 0

end Langlands.Cohomology.Lie
