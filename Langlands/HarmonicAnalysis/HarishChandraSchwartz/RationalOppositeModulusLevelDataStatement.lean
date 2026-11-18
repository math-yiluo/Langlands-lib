import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalUnipotentWeightIntegrabilityStatement

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- Actual residue-cardinality levels and the outer height comparison of
Waldspurger II.3.4, for the minimal weight on an actual opposite standard radical. -/
def RationalOppositeModulusLevelDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice S)) (ζ : cocharacterLattice S),
      IsStandardCocharacter i ν J ζ →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K),
      IsCompact (K : Set (rationalPoints G)) →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∃ L : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ → ℤ,
      Measurable L ∧
      (∀ u : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ,
        iwasawaWeight hPK (rationalMinimalModulus i ν) (u : rationalPoints G) =
        (LocalField.residueCardinality F : ℝ) ^ (-(L u : ℝ) / 2)) ∧
      LevelHeightComparison (Aubert.General.RationalPointFamily.oppositeUnipotent i ζ)
        L (LocalField.residueCardinality F : ℝ) (rationalHeight (F := F) ρ)

end Langlands.HarishChandraSchwartz
