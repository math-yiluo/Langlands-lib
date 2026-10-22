import Langlands.Geometry.Analytic.Affinoid
import Mathlib.RingTheory.Finiteness.Defs

/-! # Finite injective normalization of presented strict affinoid algebras -/

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

/-- A nonzero actual affinoid quotient receives a bounded finite injective
map from a Tate algebra with no more variables than its presentation. -/
def NoetherNormalizationStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ A : PresentedStrictAffinoidAlgebra K, Nontrivial A →
    ∃ m ≤ A.arity, ∃ g : BoundedAlgHom K (StrictTateAlgebra (Fin m) K) A,
      Function.Injective g ∧ g.toAlgHom.toRingHom.Finite

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
