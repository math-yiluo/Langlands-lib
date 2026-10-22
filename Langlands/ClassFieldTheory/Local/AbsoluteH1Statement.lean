import Langlands.ClassFieldTheory.Local.Cohomology

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Continuous Hilbert 90 for the actual algebraic-closure unit module
of a characteristic-zero field. -/
def AbsoluteH1Vanishing : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K], Subsingleton (absoluteCohomology K 1)

end Langlands.ClassFieldTheory.Local
