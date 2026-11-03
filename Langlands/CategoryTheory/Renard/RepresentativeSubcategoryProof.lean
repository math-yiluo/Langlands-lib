import Langlands.CategoryTheory.Renard.RepresentativeSubcategoryStatements
import Langlands.CategoryTheory.Renard.EquivalenceCriterion

/-!
# Renard A.II.2: proof of equivalence with selected representatives

Implementation prepared by Worker 709 and adopted by Worker 1158.
The published construction, statement and criterion are imported by name.
-/

universe v u

open CategoryTheory

namespace Langlands.Renard

theorem representativeSubcategoryEquivalence
    (C : Type u) [Category.{v} C] :
    RepresentativeSubcategoryEquivalenceStatement C := by
  apply equivalenceCriterion (RepresentativeSubcategory C) C
    (representativeInclusion C)
  · intro X Y
    exact (representativeInclusion C).map_surjective
  · intro X Y
    exact (representativeInclusion C).map_injective
  · intro X
    exact ⟨representativeOf X, ⟨representativeIso X⟩⟩

end Langlands.Renard
