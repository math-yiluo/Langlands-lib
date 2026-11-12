import Langlands.Geometry.Building.FullValidity.ChamberAxioms

/-! # The actual valuation quotient is the restricted building of the Iwahori–Tits system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Under the apartment axioms of KP Chapter 7, an actual affine Iwahori–Tits system for a
chamber `C` of the apartment (KP Theorem 7.5.3, `G(F)^0` branch) is the Tits system of KP
Axiom 4.1.9 on the existing quotient `B(G)`: its Borel subgroup `P_C` is the stabilizer of
the image of `C` in `G(F)^0`, and the facets, face relation and apartments of `B(G)` are
those of the restricted building (KP Propositions 7.6.3 and 7.6.4(1), Remark 7.6.5). -/
def AffineIwahoriTitsBuildingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal) (C : Set P.Apartment)
        (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots),
        AffineRootSystem.IsChamber P.affineRoots C → P.AffineIwahoriTitsWith C e →
          P.IsBuildingTitsSystem C P.affineTitsProjection (P.chamberSimpleInAffinePart e C)

end Langlands.Geometry.Building
