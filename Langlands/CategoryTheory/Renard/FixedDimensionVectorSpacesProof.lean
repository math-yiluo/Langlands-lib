import Langlands.CategoryTheory.Renard.FixedDimensionVectorSpacesStatements
import Langlands.CategoryTheory.Renard.EquivalenceCriterion

/-!
# Renard A.II.2: proof of the fixed-dimension vector-space equivalence

The actual full singleton inclusion is fully faithful, and the published
coordinate isomorphism supplies essential surjectivity.

Implementation by Worker 1158 following Worker 709's supplied proof route.
The published construction, statement and criterion are imported by name.
-/

universe u v

open CategoryTheory

namespace Langlands.Renard

theorem fixedDimensionVectorSpaceEquivalence
    (k : Type u) [Field k] (n : ℕ) :
    FixedDimensionVectorSpaceEquivalenceStatement.{u, v} k n := by
  apply equivalenceCriterion (OneObjectVectorSpaceCategory.{u, v} k n)
    (FixedDimensionVectorSpaces.{u, v} k n)
    (fixedDimensionVectorSpaceInclusion.{u, v} k n)
  · intro X Y
    exact (fixedDimensionVectorSpaceInclusion.{u, v} k n).map_surjective
  · intro X Y
    exact (fixedDimensionVectorSpaceInclusion.{u, v} k n).map_injective
  · intro X
    exact ⟨oneObjectVectorSpace.{u, v} k n, ⟨coordinateVectorSpaceIso.{u, v} k n X⟩⟩

end Langlands.Renard
