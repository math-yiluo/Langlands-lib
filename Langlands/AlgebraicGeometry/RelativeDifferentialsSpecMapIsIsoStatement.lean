import Langlands.AlgebraicGeometry.RelativeDifferentialsSpecMap

/-! # Invertibility of the canonical differential comparison on spectra -/

universe u

open CategoryTheory

namespace Langlands.Scheme

/-- For every commutative algebra, the canonical comparison from the associated
sheaf of algebraic differentials to the actual relative differential sheaf is
an isomorphism. -/
def RelativeDifferentialsSpecMapIsIsoStatement : Prop :=
  ∀ (R A : CommRingCat.{u}) [Algebra R A],
    IsIso (relativeDifferentialsSpecMap R A)

end Langlands.Scheme
