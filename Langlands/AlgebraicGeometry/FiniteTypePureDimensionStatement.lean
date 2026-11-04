import Langlands.AlgebraicGeometry.SchemePureDimensionAffine
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Pure dimension under arbitrary extension of the ground field -/

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Every field extension preserves and reflects componentwise pure dimension
of a finite-type commutative algebra. -/
def FiniteTypeFieldExtensionPureRingDimensionInvariance : Prop :=
  ∀ (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K]
    [CommRing A] [Algebra k K] [Algebra k A] [Algebra.FiniteType k A] (d : ℕ),
    HasPureRingDimension A d ↔ HasPureRingDimension (A ⊗[k] K) d

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
