import Langlands.BruhatTits.Cartan.ParahoricDominantQuotient
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.SpecialCompact

/-! # Corrected parahoric Cartan bijection on available Bruhat–Tits data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The actual `P_x`, positive dominant centralizer and `Z(F)^0` conclusions
of corrected KP Theorem 5.2.1, including bijectivity of the canonical map.
This property definition does not assert them for arbitrary supplied data. -/
def ParahoricCartanConclusions (B : ParahoricBuildingData G)
    (ν : cocharacterLattice B.S) (x : B.Apartment) : Prop :=
  let P := B.parahoricAt x
  let D := parahoricDominantSet B ν
  let j := rationalPoints.map B.centralizer.j
  (Set.univ = (P : Set (rationalPoints G)) * (j '' D) *
    (P : Set (rationalPoints G))) ∧
  (∀ z z' : D,
    DoubleCoset.doubleCoset (j z.val) P P =
        DoubleCoset.doubleCoset (j z'.val) P P ↔
      z'.val * z.val⁻¹ ∈ B.centralizerZero) ∧
  Function.Bijective (parahoricDominantDoubleCosetMap B ν x)

/-- Corrected KP Theorem 5.2.1 for every generic positive system and special
apartment vertex, under the full corrected Definition 4.1.26.
The quotient map is intrinsically well-defined, with its published class formula;
neither coverage nor classification is a premise of this statement. -/
def AvailableCartanStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsAvailableFor F G hG →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          ParahoricCartanConclusions B ν x

end Langlands.BruhatTits.Cartan
