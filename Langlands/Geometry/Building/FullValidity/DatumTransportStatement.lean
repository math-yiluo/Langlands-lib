import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# Transport of full corrected KP data under based group isomorphisms

This proposition states transport of supplied `KPBuildingDatum` and all its one-group
axioms. The target has the prescribed torus and inclusion. The building comparison is
equivariant along the actual rational-point map, with affine compatibility in both
directions. No construction, validity witness or assignment existence is proved here.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Derived transport target for the one-group data of corrected KP Definition 4.1.26.
For every full datum satisfying its group axioms and every commuting isomorphism square
of the ambient group and base torus, there is a full datum on the target group satisfying
the same group axioms, with exactly the prescribed torus and inclusion. Its reduced
building is equivariantly isomorphic to the source along `rationalPoints.map f.hom`;
the inverse of that same equivalence also satisfies the oriented building-isomorphism
predicate. This definition states a proposition and supplies no proof of transport. -/
def KPBuildingDatumTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (D : KPBuildingDatum G),
    D.SatisfiesGroupAxioms →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F)))
      (i : S.toGrp ⟶ H) (f : G ≅ H) (σ : D.base.S ≅ S),
      D.base.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ i →
      ∃ D' : KPBuildingDatum H,
        D'.SatisfiesGroupAxioms ∧
        D'.base.S = S ∧ HEq D'.base.i i ∧
        ∃ Φ : D.base.ReducedBuilding ≃ D'.base.ReducedBuilding,
          ValuationBuildingData.IsEquivariantBuildingIso
            D.base.toValuationBuildingData D'.base.toValuationBuildingData
            (rationalPoints.map f.hom) Φ ∧
          ValuationBuildingData.IsBuildingIso
            D'.base.toValuationBuildingData D.base.toValuationBuildingData Φ.symm

end Langlands.Geometry.Building
