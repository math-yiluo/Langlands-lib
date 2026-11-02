import Langlands.AlgebraicGeometry.Units.FiniteAlgebraRepresentabilityStatement
import Langlands.AlgebraicGeometry.Units.FiniteAlgebraAffineComparison
import Langlands.AlgebraicGeometry.Units.RelativeGlobalUnitsGluing

/-! # Representability and smoothness of actual finite-algebra units -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.FiniteAlgebraUnits

/-- The determinant-open candidate represents actual relative units on every
scheme over the field, through its specified universal unit, and is smooth. -/
theorem representability : RepresentabilityStatement.{u} := by
  intro k A _ _ _ n b
  refine ⟨?_, candidate_smooth b⟩
  exact RelativeGlobalUnits.fromUniversalUnit_isIso_of_affine
    (algebraSchemeMap k A) (candidate b) (universalUnit b)
    (fun T _ => candidateMap_affine_bijective b T)

end Langlands.AlgebraicGeometry.FiniteAlgebraUnits
