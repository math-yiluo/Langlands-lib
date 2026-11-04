import Langlands.AlgebraicGeometry.SchemePureDimensionAffine
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Pure dimension under injective flat integral extensions -/

universe u v

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- An injective flat integral algebra extension preserves and reflects
componentwise pure ring dimension, without finiteness hypotheses. -/
def FlatIntegralPureRingDimensionInvariance : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] (d : ℕ),
    HasPureRingDimension R d ↔ HasPureRingDimension S d

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
