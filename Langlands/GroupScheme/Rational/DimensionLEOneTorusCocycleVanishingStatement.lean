import Langlands.FieldTheory.DimensionLEOne
import Langlands.GroupScheme.Rational.TorusCocycleVanishing

/-! # Torus cocycle vanishing from the finite-extension norm criterion -/

universe u

namespace Langlands.GroupScheme

/-- The finite-separable norm criterion forces actual torus cocycles on
finite Galois field covers to be coboundaries. -/
def DimensionLEOneTorusCocycleVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K],
    Langlands.FieldTheory.HasDimensionLEOne K → HasTrivialTorusCocycles K

end Langlands.GroupScheme
