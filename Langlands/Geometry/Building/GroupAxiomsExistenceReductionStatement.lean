import Langlands.Geometry.Building.RootValuationBuildingConstructionStatement
import Langlands.Geometry.Building.RootGroupActionAxiomStatement
import Langlands.Geometry.Building.IwahoriDecompositionAxiomStatement
import Langlands.Geometry.Building.IntegralModelAxiomsStatement
import Langlands.Geometry.Building.GroupAxiomsExistenceStatement

/-! # The one-group clauses of corrected Definition 4.1.26 from four focused statements -/

universe u

namespace Langlands.Geometry.Building

/-- The one-group clauses of corrected KP Definition 4.1.26 (`GroupAxiomsExistenceStatement`)
follow from four focused statements, all in universe `u`:

* `RootValuationBuildingConstructionStatement`: existence of root-valuation building data with
  a polysimplicial realization and an apartment splitting satisfying the seven predicates for
  Axioms 4.1.1 (for `G` alone), 4.1.2, 4.1.4, 4.1.6 and 4.1.9;
* `RootGroupActionAxiomStatement`: Axiom 4.1.8 (2) and (3) on supplied data satisfying V 7 and
  AS 2–AS 5;
* `IwahoriDecompositionAxiomStatement`: Axiom 4.1.16 on the same supplied data;
* `IntegralModelAxiomsStatement`: Axioms 4.1.20 and 4.1.22 on supplied data satisfying the seven
  predicates.

This is a statement of the implication only; none of the five statements is asserted. -/
def GroupAxiomsExistenceReductionStatement : Prop :=
  RootValuationBuildingConstructionStatement.{u} →
    RootGroupActionAxiomStatement.{u} →
      IwahoriDecompositionAxiomStatement.{u} →
        IntegralModelAxiomsStatement.{u} →
          GroupAxiomsExistenceStatement.{u}

end Langlands.Geometry.Building
