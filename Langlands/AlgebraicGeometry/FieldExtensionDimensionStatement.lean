import Langlands.AlgebraicGeometry.SchemePureDimensionAffine
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Dimension comparisons for actual scalar-extension algebras -/

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Arbitrary extensions of the ground field preserve the total dimension of
a finitely generated commutative algebra. -/
def FiniteTypeFieldExtensionRingDimensionInvariance : Prop :=
  ∀ (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K]
    [CommRing A] [Algebra k K] [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = ringKrullDim (K ⊗[k] A)

/-- Algebraic extensions of the ground field preserve and reflect componentwise
pure dimension of an arbitrary commutative algebra. -/
def AlgebraicFieldExtensionPureRingDimensionInvariance : Prop :=
  ∀ (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K]
    [CommRing A] [Algebra k K] [Algebra k A] [Algebra.IsAlgebraic k K] (d : ℕ),
    HasPureRingDimension A d ↔ HasPureRingDimension (A ⊗[k] K) d

/-- The two distinct field-extension comparisons; neither asserts the
finite-type pure-dimension comparison for transcendental extensions. -/
def FieldExtensionDimensionComparisons : Prop :=
  FiniteTypeFieldExtensionRingDimensionInvariance.{u,v,w} ∧
    AlgebraicFieldExtensionPureRingDimensionInvariance.{u,v,w}

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
