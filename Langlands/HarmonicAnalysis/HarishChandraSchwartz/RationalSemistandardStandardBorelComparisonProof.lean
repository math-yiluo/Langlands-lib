import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardStandardComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSplitCenterIndependenceProof
import Langlands.Representation.Plancherel.DiscreteSeriesHaarComparison

/-! # Borel quotient comparison for the same standard discrete-series class -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

section StandardComparison

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [hNormalSemi : ∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [hMeasSemi : ∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [hHaarSemi : ∀ p, (mu p).IsHaarMeasure]
  {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {B : Finset (RationalPointFamily.SimpleRoot i nu) → CommGroupScheme (Spec (CommRingCat.of F))}
  (b : ∀ I, (B I).toGrp ⟶ (standardLeviModel hG hi hnu I).scheme)
  (hb : ∀ I, IsSplitComponent (b I))
  [hNormal : ∀ I, (rationalLeviSplitCenter I (b I)).Normal]
  [hMeas : ∀ I, MeasurableSpace (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  (eta : ∀ I, Measure (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I)))
  [hHaar : ∀ I, (eta I).IsHaarMeasure]

/-- The full identical-class comparison under explicit Borel quotient compatibility. -/
theorem rationalSemistandardStandardDiscreteSeriesComparison_of_borel :
    RationalSemistandardStandardDiscreteSeriesComparison.{u, uV}
      a ha mu hG hi hnu b hb eta := by
  intro hBorelSemi hBorelStd I omega
  let : SecondCountableTopology (rationalPoints G) :=
    rationalPoint_secondCountableTopology F G
  let : SecondCountableTopology (levi (standardIndex hG hi hnu I)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace (levi (standardIndex hG hi hnu I)) :=
    (isClosed_standardLeviPoints i nu (RationalPointFamily.rootSet i nu I)).locallyCompactSpace
  have hAB :
      (chosenLeviModel (standardIndex hG hi hnu I)).splitCenter
        (a (standardIndex hG hi hnu I)) = rationalLeviSplitCenter I (b I) := by
    exact splitCenterChoiceIndependence (standardIndex hG hi hnu I)
      (chosenLeviModel (standardIndex hG hi hnu I)) (standardLeviModel hG hi hnu I)
      _ _ (a (standardIndex hG hi hnu I)) (b I)
      (ha (standardIndex hG hi hnu I)) (hb I)
  exact @isDiscreteSeriesClass_borel_quotient_eq_iff.{u, uV}
    (levi (standardIndex hG hi hnu I))
    (inferInstanceAs (Group (levi (standardIndex hG hi hnu I))))
    (inferInstanceAs (TopologicalSpace (levi (standardIndex hG hi hnu I))))
    (inferInstanceAs (IsTopologicalGroup (levi (standardIndex hG hi hnu I))))
    (inferInstanceAs (LocallyCompactSpace (levi (standardIndex hG hi hnu I))))
    (inferInstanceAs (SecondCountableTopology (levi (standardIndex hG hi hnu I))))
    _ _ (hNormalSemi (standardIndex hG hi hnu I)) (hNormal I)
    ((chosenLeviModel (standardIndex hG hi hnu I)).splitCenter_le_center
      (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I)))
    (rationalLeviSplitCenter_le_center I (b I) (hb I)) hAB
    (hMeasSemi (standardIndex hG hi hnu I)) (hMeas I)
    (hBorelSemi I) (hBorelStd I)
    (mu (standardIndex hG hi hnu I)) (eta I)
    (hHaarSemi (standardIndex hG hi hnu I)) (hHaar I) omega

end StandardComparison

end Langlands.HarishChandraSchwartz
