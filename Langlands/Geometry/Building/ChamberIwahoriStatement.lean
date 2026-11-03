import Langlands.Geometry.Building.ChamberIwahori
import Langlands.Geometry.Building.ChamberSharpStatement

/-!
# Full chamber Iwahori decompositions

Full-parahoric consequences of KP 7.4.1, 7.4.3, 7.4.4 and 7.4.9,
with the fixed-sign bijections of 7.3.12(3),(5). These are Prop-valued
targets on actual data, with the corrected Chapter 7 premises explicit.
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

/-- Full Iwahori intersections and ordered multiplication at both chamber
depths. The global target below supplies the ambient and geometric premises. -/
def ChamberIwahoriConclusion (C : Set P.Apartment) (x : P.Apartment)
    (ν : cocharacterLattice P.S) : Prop :=
  P.chamberIwahori C = P.parahoricAt x ∧
  centralizerPoints P.i ⊓ P.chamberIwahori C =
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ∧
  P.iwahoriUnipotentPoints (-ν) C = P.apartment.sharpUnipotentPoints (-ν) C ∧
  P.iwahoriUnipotentPoints ν C = P.apartment.sharpUnipotentPoints ν C ∧
  Function.Injective (P.iwahoriUnipotentProduct C ν) ∧
  Set.range (P.iwahoriUnipotentProduct C ν) =
    (P.chamberIwahori C : Set (rationalPoints G)) ∧
  ∀ (strict : Bool) (nneg npos : ℕ) (aneg : Fin nneg → characterLattice P.S)
      (apos : Fin npos → characterLattice P.S),
    Function.Injective aneg →
    Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν) →
    Function.Injective apos →
    Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν →
    Function.Injective (P.apartment.orderedChamberBlockProduct x strict aneg) ∧
    Set.range (P.apartment.orderedChamberBlockProduct x strict aneg) =
      (P.iwahoriUnipotentPoints (-ν) C : Set (rationalPoints G)) ∧
    Function.Injective (P.apartment.orderedChamberBlockProduct x strict apos) ∧
    Set.range (P.apartment.orderedChamberBlockProduct x strict apos) =
      (P.iwahoriUnipotentPoints ν C : Set (rationalPoints G)) ∧
    Function.Injective (P.orderedIwahoriChamberProduct x strict aneg apos) ∧
    Set.range (P.orderedIwahoriChamberProduct x strict aneg apos) =
      (P.chamberIwahori C : Set (rationalPoints G))

/-- Full-Iwahori facet products, with negative depth `0+`, central factor
`Z(F)^0`, and positive depth `0`. The global target retains the required
positive-system choice for a face of the chamber. -/
def ChamberIwahoriFacetConclusion (Fa C : Set P.Apartment)
    (ν : cocharacterLattice P.S) : Prop :=
  ∀ (nneg npos : ℕ) (aneg : Fin nneg → characterLattice P.S)
      (apos : Fin npos → characterLattice P.S),
    Function.Injective aneg →
    Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν) →
    Function.Injective apos →
    Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν →
    Function.Injective (P.apartment.orderedFacetBlockProduct Fa true aneg) ∧
    Set.range (P.apartment.orderedFacetBlockProduct Fa true aneg) =
      (P.iwahoriUnipotentPoints (-ν) C : Set (rationalPoints G)) ∧
    Function.Injective (P.apartment.orderedFacetBlockProduct Fa false apos) ∧
    Set.range (P.apartment.orderedFacetBlockProduct Fa false apos) =
      (P.iwahoriUnipotentPoints ν C : Set (rationalPoints G)) ∧
    Function.Injective (P.orderedIwahoriFacetProduct Fa aneg apos) ∧
    Set.range (P.orderedIwahoriFacetProduct Fa aneg apos) =
      (P.chamberIwahori C : Set (rationalPoints G))

/-- KP 7.4.9 on the actual sharp chamber group, together with its full
parahoric consequences using `Z(F)^0`. This retains corrected Chapter 7
AS 5, chamber membership, genericity, and the facet sign condition.
It asserts neither existence of the data nor any of the conclusions as
a premise. Compact openness is a separate target. -/
def ChamberIwahoriDecompositionStatement : Prop :=
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
  ∀ (C : Set P.Apartment) (x : P.Apartment) (ν : cocharacterLattice P.S),
    AffineRootSystem.IsChamber P.affineRoots C →
    x ∈ C →
    IsGenericCocharacter P.i ν →
    P.apartment.ChamberSharpConclusion C x ν ∧
    P.ChamberIwahoriConclusion C x ν ∧
      ∀ Fa : Set P.Apartment,
        AffineRootSystem.IsFaceOf P.affineRoots Fa C →
        P.apartment.FacetChamberPositiveSystem Fa C ν →
        P.apartment.ChamberSharpFacetConclusion Fa C x ν ∧
          P.ChamberIwahoriFacetConclusion Fa C ν

end Langlands.Geometry.Building.ParahoricBuildingData
