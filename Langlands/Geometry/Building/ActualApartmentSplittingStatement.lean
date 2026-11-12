import Langlands.Geometry.Building.FullValidity.AffineApartment
import Langlands.Geometry.Building.ValuationBuildingAxioms

/-! # Existence of the actual affine apartment splitting of KP Axiom 4.1.4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For actual valuation-building data `B` of a group over a nonarchimedean local field whose
apartment class satisfies the Chapter 7 apartment axioms, there are actual splitting data `T`
(the derived subgroup `G_der`, a maximal split torus `S'` of `G_der` inside `S`, and the split
component `A_G` of `G` inside `S`) satisfying the clauses (A 0)–(A 2) of KP Axiom 4.1.4. -/
def ActualApartmentSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (B : ValuationBuildingData G),
    B.SatisfiesApartmentAxioms →
      ∃ T : B.ApartmentSplitting, B.SatisfiesAffineApartmentAxiom T

end Langlands.Geometry.Building
