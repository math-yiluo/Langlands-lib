import Langlands.Geometry.Building.ChamberRootProducts
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.GroupScheme.Rational.RootProductStatement

/-!
# Sharp chamber decompositions

The fixed-apartment specialization of KP Corollary 7.4.9, with the factor
bijections of Proposition 7.3.12(3),(5), at depths `0` and `0+` and for a
facet in the chamber closure. The source hypotheses, including corrected
AS 5, are explicit in `ValuationBuildingData.ChamberSharpDecompositionStatement`.
This is a statement, not a proof or an existence assertion.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The conclusion at both depths of KP 7.4.9, with fixed-sign
bijections from 7.3.12(3),(5). Its source premises occur in
`ValuationBuildingData.ChamberSharpDecompositionStatement`. -/
def ChamberSharpConclusion (C : Set D.Apartment) (x : D.Apartment)
    (ν : cocharacterLattice S) : Prop :=
  (∀ a ∈ relativeRoots i,
    D.rootFixer a C = D.filtration x a 0 ∧
    D.rootFixerPlus a C = D.filtrationPlus x a 0 ∧
    D.filtration x a 0 = D.filtrationPlus x a 0 ∧
    ∀ strict : Bool,
      D.chamberRootBlock x strict a = (D.chamberRootGroup x strict a :
        Set (rationalPoints G))) ∧
  D.sharpNormalizer {x} = D.sharpCentralizer {x} ∧
  Function.Injective (D.sharpUnipotentProduct C x ν) ∧
  Set.range (D.sharpUnipotentProduct C x ν) =
    (D.sharpFixer C : Set (rationalPoints G)) ∧
  ∀ (strict : Bool) (nneg npos : ℕ) (aneg : Fin nneg → characterLattice S)
      (apos : Fin npos → characterLattice S),
    Function.Injective aneg →
    Set.range aneg = RelativeRoot.indivisiblePositiveRoots i (-ν) →
    Function.Injective apos →
    Set.range apos = RelativeRoot.indivisiblePositiveRoots i ν →
    Function.Injective (D.orderedChamberBlockProduct x strict aneg) ∧
    Set.range (D.orderedChamberBlockProduct x strict aneg) =
      (D.sharpUnipotentPoints (-ν) C : Set (rationalPoints G)) ∧
    Function.Injective (D.orderedChamberBlockProduct x strict apos) ∧
    Set.range (D.orderedChamberBlockProduct x strict apos) =
      (D.sharpUnipotentPoints ν C : Set (rationalPoints G)) ∧
    Function.Injective (D.orderedSharpChamberProduct x strict aneg apos) ∧
    Set.range (D.orderedSharpChamberProduct x strict aneg apos) =
      (D.sharpFixer C : Set (rationalPoints G))

/-- The facet constancy needed to identify the intersection definitions with
KP's point-independent notation `U_{a,F,0}` and `U_{a,F,0+}`. -/
def RootFacetConstancyConclusion (F : Set D.Apartment) : Prop :=
  ∀ a ∈ relativeRoots i, ∀ y ∈ F,
    D.rootFixer a F = D.filtration y a 0 ∧
    D.rootFixerPlus a F = D.filtrationPlus y a 0

/-- The facet comparison and ordered bijections of KP 7.4.9, using 6.3.21
and 7.3.12(3),(5). The complete statement below requires a face of a
chamber, a point in that chamber, a generic cocharacter and the geometric
positive-system choice, together with the fixed-apartment axioms. -/
def ChamberSharpFacetConclusion (F C : Set D.Apartment) (x : D.Apartment)
    (ν : cocharacterLattice S) : Prop :=
  D.RootFacetConstancyConclusion F ∧
  (∀ a ∈ relativeRoots i,
    D.rootFixerPlus a F ≤ D.rootFixerPlus a C ∧
    D.rootFixerPlus a C ≤ D.rootFixer a C ∧
    D.rootFixer a C ≤ D.rootFixer a F ∧
    (∀ strict : Bool,
      D.facetRootBlock F strict a = (D.facetRootGroup F strict a :
        Set (rationalPoints G))) ∧
    (0 < latticePairing S a ν → D.rootFixer a F = D.rootFixer a C) ∧
    (latticePairing S a ν < 0 → D.rootFixerPlus a F = D.rootFixer a C)) ∧
  ∀ (nneg npos : ℕ) (aneg : Fin nneg → characterLattice S)
      (apos : Fin npos → characterLattice S),
    Function.Injective aneg →
    Set.range aneg = RelativeRoot.indivisiblePositiveRoots i (-ν) →
    Function.Injective apos →
    Set.range apos = RelativeRoot.indivisiblePositiveRoots i ν →
    Function.Injective (D.orderedFacetBlockProduct F true aneg) ∧
    Set.range (D.orderedFacetBlockProduct F true aneg) =
      (D.sharpUnipotentPoints (-ν) C : Set (rationalPoints G)) ∧
    Function.Injective (D.orderedFacetBlockProduct F false apos) ∧
    Set.range (D.orderedFacetBlockProduct F false apos) =
      (D.sharpUnipotentPoints ν C : Set (rationalPoints G)) ∧
    Function.Injective (D.orderedSharpFacetProduct F x aneg apos) ∧
    Set.range (D.orderedSharpFacetProduct F x aneg apos) =
      (D.sharpFixer C : Set (rationalPoints G))

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- KP Corollary 7.4.9 and the bijections from 7.3.12(3),(5), on the actual
fixed apartment of a connected reductive group over a nonarchimedean
local field. `SatisfiesApartmentAxioms` explicitly retains V 6, V 7,
the affine-root-system laws and corrected AS 5. The facet clause retains
the geometric positive-system requirement of Fact 7.4.6.

The assertion concerns the sharp root-generated group. It supplies
neither the full parahoric nor the existence of data satisfying its
premises for every connected reductive group. -/
def ChamberSharpDecompositionStatement : Prop :=
  B.apartment.SatisfiesApartmentAxioms B.centralizer →
  ∀ (C : Set B.Apartment) (x : B.Apartment) (ν : cocharacterLattice B.S),
    AffineRootSystem.IsChamber B.affineRoots C →
    x ∈ C →
    IsGenericCocharacter B.i ν →
    B.apartment.ChamberSharpConclusion C x ν ∧
      ∀ F : Set B.Apartment,
        AffineRootSystem.IsFaceOf B.affineRoots F C →
        B.apartment.FacetChamberPositiveSystem F C ν →
        B.apartment.ChamberSharpFacetConclusion F C x ν

end Langlands.Geometry.Building.ValuationBuildingData
