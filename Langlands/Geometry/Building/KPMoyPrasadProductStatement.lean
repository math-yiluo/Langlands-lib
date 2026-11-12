import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.GroupScheme.Rational.RootProductStatement

/-!
# KP Proposition 13.2.5(3) on supplied data

The ordered product of the indivisible-root blocks `U_{a,x,r} U_{2a,x,r}` of one sign, the
filtration subgroup `Z(F)_r` and the blocks of the other sign, and the statement that it is a
bijection onto the Moy–Prasad subgroup `P_{x,r}` for `r > 0`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

/-- Multiply, in the given orders, one element of each block `U_{a,x,r} U_{2a,x,r}` for the
roots `aneg j`, then an element of `Z(F)_r`, then one element of each block for the roots
`apos j` (KP Proposition 13.2.5(3) with the blocks of Definition 7.3.3(1) at constant depth
`r`). No sign, completeness or bijectivity condition is built in. -/
def orderedMoyPrasadProduct (x : P.Apartment) (r : NNReal) {nneg npos : ℕ}
    (aneg : Fin nneg → characterLattice P.S) (apos : Fin npos → characterLattice P.S)
    (p : (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
      Zf.filtration r × (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j))) :
    rationalPoints G :=
  P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg p.1 *
    rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos p.2.2

end ParahoricBuildingData.CentralizerFiltration

/-- **KP Proposition 13.2.5(3)** for supplied data, with indivisible-root blocks. For `r > 0`,
every positive system (given by a generic cocharacter `ν`) and all orders of the indivisible
roots of each sign, the ordered product of the negative blocks, `Z(F)_r` and the positive
blocks is a bijection onto `P_{x,r}`. -/
def MoyPrasadProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      ∀ (x : P.Apartment) (r : NNReal), 0 < r →
      ∀ (ν : cocharacterLattice P.S), IsGenericCocharacter P.i ν →
      ∀ (nneg npos : ℕ) (aneg : Fin nneg → characterLattice P.S)
        (apos : Fin npos → characterLattice P.S),
        Function.Injective aneg →
        Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν) →
        Function.Injective apos →
        Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν →
        Function.Injective (Zf.orderedMoyPrasadProduct x r aneg apos) ∧
          Set.range (Zf.orderedMoyPrasadProduct x r aneg apos) =
            (Zf.moyPrasad x r : Set (rationalPoints G))

end Langlands.Geometry.Building
