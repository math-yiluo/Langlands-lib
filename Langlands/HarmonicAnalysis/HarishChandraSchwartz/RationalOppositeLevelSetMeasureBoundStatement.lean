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

/-- Waldspurger II.4.1 for actual measurable modulus levels on the opposite radical. -/
def RationalOppositeLevelSetMeasureBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice S)) (ζ : cocharacterLattice S),
      IsStandardCocharacter i ν J ζ →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
      Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K),
      IsCompact (K : Set (rationalPoints G)) →
    ∀ (nuU : Measure (Aubert.General.RationalPointFamily.oppositeUnipotent i ζ))
      [nuU.IsHaarMeasure]
      (L : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ → ℤ),
      Measurable L →
      (∀ u : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ,
        iwasawaWeight hPK (rationalMinimalModulus i ν) (u : rationalPoints G) =
        (LocalField.residueCardinality F : ℝ) ^ (-(L u : ℝ) / 2)) →
      LevelSetMeasureBound nuU L (LocalField.residueCardinality F : ℝ)

end Langlands.HarishChandraSchwartz
