import Langlands.Geometry.Building.KPParahoric
import Langlands.Geometry.Building.ChamberRootProducts

/-!
# Chamber Iwahori and full central-factor multiplication maps

`chamberIwahori C` is the actual `P_C`. The maps below multiply actual
negative, `Z(F)^0`, and positive factors in `G(F)`; their injectivity and
ranges are separate assertions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual chamber Iwahori `I_C = P_C` (KP Definition 7.4.5(2)).
The construction is total on subsets; its Iwahori interpretation requires
`C` to be a chamber. -/
abbrev chamberIwahori (C : Set P.Apartment) : Subgroup (rationalPoints G) :=
  P.parahoric C

/-- The actual Dynamic unipotent radical intersected with the full `I_C`.
For a generic cocharacter this is the chosen minimal-parabolic radical
in the intended connected-reductive scope. -/
def iwahoriUnipotentPoints (ν : cocharacterLattice P.S) (C : Set P.Apartment) :
    Subgroup (rationalPoints G) :=
  (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) ⊓
    P.chamberIwahori C

/-- Negative/full-central/positive multiplication on actual Iwahori
unipotent intersections. The central element is mapped by the actual
centralizer inclusion `j : Z_G(S) → G`. -/
def iwahoriUnipotentProduct (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (p : P.iwahoriUnipotentPoints (-ν) C × P.centralizerZero ×
      P.iwahoriUnipotentPoints ν C) : rationalPoints G :=
  (p.1 : rationalPoints G) *
    rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      (p.2.2 : rationalPoints G)

/-- Ordered point-block multiplication at `0` or `0+`, with full central
factor `Z(F)^0`. Each block retains its actual doubled-root factor. -/
def orderedIwahoriChamberProduct (x : P.Apartment) (strict : Bool)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (p : (∀ j, P.apartment.chamberRootBlock x strict (aneg j)) ×
      P.centralizerZero × (∀ j, P.apartment.chamberRootBlock x strict (apos j))) :
    rationalPoints G :=
  P.apartment.orderedChamberBlockProduct x strict aneg p.1 *
    rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      P.apartment.orderedChamberBlockProduct x strict apos p.2.2

/-- Ordered facet-block multiplication with negative depth `0+`, full
central factor `Z(F)^0`, and positive depth `0`. Its chamber-range
interpretation requires the geometric positive-system choice. -/
def orderedIwahoriFacetProduct (Fa : Set P.Apartment)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (p : (∀ j, P.apartment.facetRootBlock Fa true (aneg j)) ×
      P.centralizerZero × (∀ j, P.apartment.facetRootBlock Fa false (apos j))) :
    rationalPoints G :=
  P.apartment.orderedFacetBlockProduct Fa true aneg p.1 *
    rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      P.apartment.orderedFacetBlockProduct Fa false apos p.2.2

end Langlands.Geometry.Building.ParahoricBuildingData
