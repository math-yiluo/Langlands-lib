import Langlands.Cohomology.AcyclicResolution.Comparison

/-!
# Independence of the resolution comparison from the injective resolution

Proof of `Langlands.Cohomology.ResolutionComparisonIndependenceStatement`: for a right
resolution `ε : A[0] ⟶ K` and augmentation-compatible lifts `φ : K ⟶ I` and `ψ : K ⟶ J` to
two injective resolutions of `A`, the maps `Hⁿ(F K) ⟶ Rⁿ F A` built from `(I, φ)` and from
`(J, ψ)` agree. The statement's expression is the Library's
`AcyclicResolution.comparison F I φ n`, and the proof applies
`AcyclicResolution.comparison_eq`.
-/

open CategoryTheory

namespace Langlands.Cohomology

universe u v u' v'

/-- The comparison of a right resolution with the right derived functors depends neither on
the injective resolution nor on the augmentation-compatible lift. -/
theorem resolutionComparisonIndependenceStatement :
    ResolutionComparisonIndependenceStatement.{u, v, u', v'} := by
  intro C _ _ _ D _ _ F _ A K ε _ I J φ ψ hφ hψ n
  exact AcyclicResolution.comparison_eq F ε φ ψ hφ hψ n

end Langlands.Cohomology
