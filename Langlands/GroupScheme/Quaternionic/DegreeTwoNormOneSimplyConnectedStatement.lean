import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Simple connectedness of actual degree-two reduced-norm-one groups -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.GroupScheme.CentralSimpleUnits

/-- Actual reduced-norm-one groups of central simple algebras of dimension four
are algebraically simply connected, with no characteristic restriction. -/
def DegreeTwoNormOneSimplyConnectedStatement : Prop :=
  ∀ (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A],
    Module.finrank K A = 4 → IsSimplyConnected (normOne K A)

end Langlands.GroupScheme.CentralSimpleUnits
