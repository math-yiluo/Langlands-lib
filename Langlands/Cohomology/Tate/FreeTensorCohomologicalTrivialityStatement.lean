import Langlands.Cohomology.Tate.CohomologicallyTrivial
import Langlands.Cohomology.Tate.TensorShifts
import Mathlib.LinearAlgebra.FreeModule.Basic

open CategoryTheory
open scoped MonoidalCategory

universe u

namespace Langlands.Tate

/-- Tensoring cohomologically trivial integral coefficients with a free
integral representation preserves cohomological triviality. -/
def FreeTensorCohomologicalTriviality : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (A B : Rep.{u} IntegralScalar.{u} G) [Module.Free IntegralScalar.{u} B],
    IsCohomologicallyTrivial A → IsCohomologicallyTrivial (A ⊗ B)

end Langlands.Tate
