import Langlands.GroupScheme.Rational.SemigroupRealizationGeometry
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.TorusUnipotenceProof
import Langlands.GroupScheme.Rational.TorusSplitUnipotenceProof

/-! # Realization of the actual semigroup subgroup -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- The actual generated semigroup subgroup has the full geometric, maximality
and split-unipotence properties of the published realization statement. -/
theorem semigroupRealization : SemigroupRealizationStatement.{u} := by
  intro k _ G hG hAff S hS b
  let := hG
  let := hAff
  intro A
  refine ⟨isSmoothConnectedClosed_semigroupSubgroup b hS A,
    semigroupSubgroup_isStable b A,
    hasLieImage_semigroupSubgroup b hS A, ?_, ?_, ?_⟩
  · intro H j hj hzero
    exact semigroupSubgroup_unipotent_and_split_of_hasLieImage b hS
      torusActionUnipotence torusActionSplitUnipotence A
      (isSmoothConnectedClosed_semigroupSubgroup b hS A)
      (hasLieImage_semigroupSubgroup b hS A) hj hzero
  · intro F hF hstable
    exact semigroupSubgroup_maximality b hS A F hF hstable
  · intro F hF hstable hLie
    exact eq_semigroupSubgroup_of_exact_lieImage b hS A hF hstable hLie

end Langlands.GroupScheme.RelativeRoot
