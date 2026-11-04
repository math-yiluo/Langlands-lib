import Langlands.AlgebraicGeometry.LocalTopologicalDimension
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Local dimension under extension of the ground field -/

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Extending the ground field preserves local dimension at every actual prime
of a finite-type algebra. -/
def FiniteTypeFieldExtensionLocalDimensionInvariance : Prop :=
  ∀ (k : Type u) (K : Type v) (A : Type w)
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
    [Algebra.FiniteType k A] (q : PrimeSpectrum (K ⊗[k] A)),
    topologicalKrullDimAt q =
      topologicalKrullDimAt (q.comap Algebra.TensorProduct.includeRight.toRingHom)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
