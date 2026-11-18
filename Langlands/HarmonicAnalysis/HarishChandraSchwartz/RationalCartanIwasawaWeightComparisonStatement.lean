import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound

/-! # Actual Cartan-to-Iwasawa weight comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The actual-point modulus comparison underlying Waldspurger's Lemma II.3.2,
with arbitrary compact factors and a finite family in the torus centralizer. -/
def RationalCartanIwasawaWeightComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), IsCompact (K0 : Set (rationalPoints G)) →
    ∀ (F0 : Finset (centralizerPoints i)) (K : Subgroup (rationalPoints G)),
      IsOpen (K : Set (rationalPoints G)) → IsCompact (K : Set (rationalPoints G)) →
    ∀ hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K,
    ∃ C : ℝ, 0 < C ∧ ∀ y : cocharacterLattice S,
      (∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
        0 ≤ Aubert.General.simpleRootPairing i ν β y) →
      ∀ g ∈ rationalCartanCell i K0 F0 y,
        iwasawaWeight hPK (rationalMinimalModulus i ν)
            (Aubert.General.uniformizerPowers i (.ofAdd y)) ≤
          C * iwasawaWeight hPK (rationalMinimalModulus i ν) g

end Langlands.HarishChandraSchwartz
