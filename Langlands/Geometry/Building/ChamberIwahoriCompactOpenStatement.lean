import Langlands.Geometry.Building.ChamberIwahori
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.GroupScheme.Rational.PointTopology

/-!
# Compact openness of the actual chamber Iwahori

The local-field consequence of KP 7.3.14, 7.4.4 and Fact 2.2.3,
in the canonical topology on actual rational points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual chamber Iwahori `I_C = P_C` is compact and open in the
canonical rational-point topology. The fixed-apartment hypotheses include
V 6, V 7 and the corrected Chapter 7 AS 5. This is a statement target;
it assumes neither compact openness nor bounded open stabilizers. -/
def ChamberIwahoriCompactOpenStatement : Prop :=
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ∀ C : Set P.Apartment,
    AffineRootSystem.IsChamber P.affineRoots C →
    IsCompact (P.chamberIwahori C : Set (rationalPoints G)) ∧
      IsOpen (P.chamberIwahori C : Set (rationalPoints G))

end Langlands.Geometry.Building.ParahoricBuildingData
