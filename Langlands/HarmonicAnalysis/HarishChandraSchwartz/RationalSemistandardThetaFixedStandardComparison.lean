import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixed
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardStandardComparison

/-! # Full fixed indices restrict to the published standard fixed indices -/

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
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {B : Finset (RationalPointFamily.SimpleRoot i nu) → CommGroupScheme (Spec (CommRingCat.of F))}
  (b : ∀ I, (B I).toGrp ⟶ Standard.leviScheme i nu (RationalPointFamily.rootSet i nu I))
  (hb : ∀ I, IsSplitComponent (b I))
  [hNormal : ∀ I, (rationalLeviSplitCenter I (b I)).Normal]
  [hMeas : ∀ I, MeasurableSpace (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I) ⧸ rationalLeviSplitCenter I (b I))]
  (eta : ∀ I, Measure (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I) ⧸ rationalLeviSplitCenter I (b I)))
  [hHaar : ∀ I, (eta I).IsHaarMeasure]

variable [∀ I, BorelSpace
      (levi (standardIndex hG hi hnu I) ⧸
        (chosenLeviModel (standardIndex hG hi hnu I)).splitCenter
          (a (standardIndex hG hi hnu I)))]
    [∀ I, BorelSpace
      (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]

variable (hds : RationalSemistandardStandardDiscreteSeriesComparison.{u, uV}
  a ha mu hG hi hnu b hb eta)

/-- The actual full-to-standard index comparison preserves and reflects
membership in the fixed-index sets at every subgroup level, using the
same-class discrete-series comparison on its two Borel-compatible quotient families. -/
theorem rationalStandardFullIndex_mem_fixed_iff
    (H : Subgroup (rationalPoints G)) (t : RationalStandardTheta.{u, uV} b hb eta) :
    rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds t ∈
        rationalSemistandardThetaFixed.{u, uV} a ha mu H ↔
      t ∈ rationalThetaFixed.{u, uV} hG hi hnu b hb eta H := by
  rcases t with ⟨I, O⟩
  rw [mem_rationalSemistandardThetaFixed, mem_rationalThetaFixed]
  constructor
  · rintro ⟨w, hw, hQ⟩
    refine ⟨(rationalStandardFullDiscreteSeriesEquiv a ha mu hG hi hnu b hb eta hds I).symm w,
      hw, ?_⟩
    apply (rationalStandardFullOrbitEquiv a ha mu hG hi hnu b hb eta hds I).injective
    change Quotient.mk _ w = _
    exact hQ
  · rintro ⟨w, hw, hQ⟩
    refine ⟨rationalStandardFullDiscreteSeriesEquiv a ha mu hG hi hnu b hb eta hds I w,
      hw, ?_⟩
    exact (rationalStandardFullOrbitEquiv_mk a ha mu hG hi hnu b hb eta hds I w).symm.trans
      (congrArg (rationalStandardFullOrbitEquiv a ha mu hG hi hnu b hb eta hds I) hQ)

/-- Restriction to the existing standard index gives exactly the old fixed set,
with the two Borel-compatible quotient families of the comparison map. -/
theorem rationalSemistandardThetaFixed_standard_preimage (H : Subgroup (rationalPoints G)) :
    (rationalStandardFullIndex.{u, uV} a ha mu hG hi hnu b hb eta hds) ⁻¹'
        rationalSemistandardThetaFixed.{u, uV} a ha mu H =
      rationalThetaFixed.{u, uV} hG hi hnu b hb eta H := by
  ext t
  exact rationalStandardFullIndex_mem_fixed_iff a ha mu hG hi hnu b hb eta hds H t

include hds in
/-- Full fixed-index finiteness transfers to the existing standard set by the
published finite-fiber index map on the two Borel-compatible quotient families.
No ambient or Levi finiteness premise is added. -/
theorem finite_rationalThetaFixed_of_full (H : Subgroup (rationalPoints G))
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite) :
    (rationalThetaFixed.{u, uV} hG hi hnu b hb eta H).Finite := by
  rw [← rationalSemistandardThetaFixed_standard_preimage a ha mu hG hi hnu b hb eta hds H]
  exact hfin.preimage' fun t _ =>
    rationalStandardFullIndex_finite_fibers a ha mu hG hi hnu b hb eta hds t

end StandardComparison

end Langlands.HarishChandraSchwartz
