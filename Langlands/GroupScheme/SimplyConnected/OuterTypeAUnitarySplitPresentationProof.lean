import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitReduction
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleReduction
import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof

/-! # Outer type A groups with split unitary algebras are special unitary groups

Proof of `OuterTypeAUnitarySplitPresentationStatement`, by composing two published
conditional reductions with the published classification of torus-preserving
automorphisms of the split special linear group.
-/

universe u

namespace Langlands.GroupScheme

/-- **Outer type A groups with split unitary algebras.** An outer type A group
whose unitary involution algebras split is the special unitary group of a
nonsingular Hermitian matrix over its star field. -/
theorem outerTypeAUnitarySplitPresentation :
    OuterTypeAUnitarySplitPresentationStatement.{u} :=
  OuterTypeAUnitarySplit.outerTypeAUnitarySplitPresentation_of_specialLinearTitsCocycle
    (specialLinearTitsCocycle_of_torusAutomorphism
      SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism)

end Langlands.GroupScheme
