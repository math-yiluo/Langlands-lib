import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound

/-! # Actual Cartan–Iwasawa weight comparison from standard-basis data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The Cartan–Iwasawa weight comparison on the cells of a compact open subgroup
with a simultaneous standard basis, for an independently supplied Iwasawa pair. -/
def RationalCartanIwasawaWeightComparisonOfBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    ∀ (ν : cocharacterLattice S) (K0 : Subgroup (rationalPoints G)),
      IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
    ∀ (F0 : Finset (centralizerPoints i)) (K : Subgroup (rationalPoints G)),
      IsOpen (K : Set (rationalPoints G)) → IsCompact (K : Set (rationalPoints G)) →
    ∀ hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K,
    ∃ C : ℝ, 0 < C ∧ ∀ y : cocharacterLattice S,
      (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) →
      ∀ g ∈ rationalCartanCell i K0 F0 y,
        iwasawaWeight hPK (rationalMinimalModulus i ν) (uniformizerPowers i (.ofAdd y)) ≤
          C * iwasawaWeight hPK (rationalMinimalModulus i ν) g

end Langlands.HarishChandraSchwartz
