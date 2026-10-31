import Langlands.Cohomology.PerfectModuleComplex

set_option autoImplicit false

universe u

open CategoryTheory

namespace Langlands.Cohomology.ModuleComplex

/-- Extension by zero of a bounded natural-number-indexed finite projective
complex is a strictly perfect integer-indexed complex. -/
def BoundedNatComplexExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ),
    (∀ i : ℕ, n < i → Subsingleton (K.X i)) →
    (∀ i : ℕ, Module.Finite R (K.X i) ∧ Module.Projective R (K.X i)) →
    IsStrictlyPerfect (K.extend ComplexShape.embeddingUpNat)

end Langlands.Cohomology.ModuleComplex
