import Langlands.Geometry.Building.DoubleCosetStatementReduction
import Langlands.Geometry.Building.IwahoriWeylProof
import Langlands.Geometry.Building.FacetParabolicComparisonProof

/-! # Proof of the parahoric double-coset bijection (KP Theorem 7.8.1(3))

The published reduction `parahoricDoubleCosetStatement_of_statements` derives
`ParahoricDoubleCosetStatement` from the chamber splitting of KP 7.8.2 and the
common-chamber facet-parabolic comparison of KP Proposition 7.5.5. Both are proved in the
Library: `iwahoriWeylChamberSplitting` and `facetParabolicComparison`. The equivalence is
built on the Iwahori equivalence of the corrected KP Theorem 7.8.1(2), whose injectivity
follows the authors' 2024 corrections.
-/

universe u

namespace Langlands.Geometry.Building

/-- **KP Theorem 7.8.1(3).** For parahoric building data satisfying the apartment axioms and
facets `F₁`, `F₂` in the closure of a common chamber `C`, `Z(F)^0` is normal in `N(F)` and the
map `W^aff_{F₁}\W̃^0/W^aff_{F₂} → P_{F₁}\G(F)/P_{F₂}`, `n ↦ P_{F₁} n P_{F₂}`, is a
bijection. -/
theorem parahoricDoubleCoset : ParahoricDoubleCosetStatement.{u} :=
  parahoricDoubleCosetStatement_of_statements iwahoriWeylChamberSplitting
    facetParabolicComparison

end Langlands.Geometry.Building
