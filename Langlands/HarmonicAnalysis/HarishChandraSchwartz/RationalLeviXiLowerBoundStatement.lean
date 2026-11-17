import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds

/-! # The lower bound of Lemma II.1.1 in an actual standard Levi -/

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

/-- The lower spherical bound on the full Levi chamber, including finitely
many centralizer translates and an arbitrary compact open Levi Iwasawa factor. -/
def RationalLeviXiLowerBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (K.subgroupOf (standardLeviPoints i ν J)))
      (F0 : Finset (centralizerPoints i)),
    ∃ C : ℝ, 0 < C ∧ ∀ m : standardLeviPoints i ν J,
      (∃ f ∈ F0, ∃ a : rationalPoints S.toGrp,
        a ∈ CocharacterUniformizer.CAplus F S J ∧
          (m : rationalPoints G) = (f : rationalPoints G) * rationalPoints.map i a) →
      iwasawaWeight hM (standardLeviMinimalModulusOf i ν J) m ≤
        C * rationalLeviXi hKc hM m

end Langlands.HarishChandraSchwartz
