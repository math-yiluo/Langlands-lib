import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock

/-! # Nilpotence and commutation on actual generalized-weight blocks -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- The actual normalized generator differences on each generalized-weight block
commute and are annihilated by the ambient dimension. This is a statement. -/
def CommutingTupleNormalizedBlockNilpotenceStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ),
    (∀ i : Fin d, normalizedGeneratorDifference A c i ^ Module.finrank ℂ V = 0) ∧
      ∀ i j : Fin d,
        Commute (normalizedGeneratorDifference A c i) (normalizedGeneratorDifference A c j)

end Langlands
