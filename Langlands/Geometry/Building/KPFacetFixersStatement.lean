import Langlands.Geometry.Building.ChamberIwahori
import Langlands.Geometry.Building.KPApartmentAxioms

/-!
# Constancy of the actual full parahoric on a facet

The facet comparison used to pass from a chamber parahoric to a point parahoric.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- KP Lemma 7.4.4(1), for the actual full parahoric with its central factor. -/
def FacetFixerConstancyStatement : Prop :=
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
  ∀ Fa : Set P.Apartment,
    AffineRootSystem.IsFacet P.affineRoots Fa →
    ∀ x ∈ Fa, P.parahoric Fa = P.parahoricAt x

end Langlands.Geometry.Building.ParahoricBuildingData
