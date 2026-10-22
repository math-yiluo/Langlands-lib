import Langlands.ClassFieldTheory.Local.Cohomology

/-! # Finite-relative Hilbert 90 over lifted integer scalars -/

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- First cohomology of the actual automorphism action on units vanishes for
every finite field extension, with independent base and extension universes. -/
def FiniteRelativeH1Vanishing : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], Subsingleton (relativeCohomology K L 1)

end Langlands.ClassFieldTheory.Local
