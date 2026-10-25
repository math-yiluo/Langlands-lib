import Langlands.Algebra.CechEqualizer.Definitions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # The noetherian core of the smooth equalizer fibre criterion -/

universe u v w z

namespace Langlands.Algebra.CechEqualizer

/-- Over a noetherian base, goodness of the associated-prime residue fields
implies goodness of a module for a differential between a faithfully flat
algebra and a flat algebra. -/
def NoetherianGoodCriterion : Prop :=
  ∀ (A₀ : Type u) (C₀ : Type v) (C₁ : Type w) (N : Type z)
    [CommRing A₀] [CommRing C₀] [CommRing C₁] [Algebra A₀ C₀] [Algebra A₀ C₁]
    [AddCommGroup N] [Module A₀ N] (d : C₀ →ₗ[A₀] C₁),
    d 1 = 0 → Module.FaithfullyFlat A₀ C₀ → Module.Flat A₀ C₁ →
    IsNoetherianRing A₀ →
    (∀ (q : Ideal A₀) [q.IsPrime], q ∈ associatedPrimes A₀ N → Good d q.ResidueField) →
    Good d N

end Langlands.Algebra.CechEqualizer
