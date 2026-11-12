import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Data satisfying the one-group clauses of corrected Definition 4.1.26 exist -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For every connected reductive group `G` over a nonarchimedean local field `F` there are data
`D : KPBuildingDatum G` (building, polysimplicial structure, splitting, integral models, special
fibre quotients, relative root data) satisfying every clause of the ten axioms of corrected KP
Definition 4.1.26 that concerns `G` alone (`KPBuildingDatum.SatisfiesGroupAxioms`): Axiom 4.1.1
for `G` alone and Axioms 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.20 and 4.1.22. The
comparisons between groups of Axioms 4.1.1 and 4.1.17 are not part of this statement. -/
def GroupAxiomsExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsConnectedReductive G → ∃ D : KPBuildingDatum G, D.SatisfiesGroupAxioms

end Langlands.Geometry.Building
