import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitFinitenessByRank
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalRankZeroOrbitFinitenessProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierReconstruction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierDetection

/-! # Relative-rank induction for orbit finiteness and Fourier injectivity -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard RationalSemistandard.FourierInversion

/-- The zero case of VIII.1 (2) on every actual group of exact relative
semisimple rank `n`. -/
def RationalExactRankFourierInjectivityStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    relativeRootRank i = n → RationalLocalFourierInjectivityStatement.{u, uV} G

/-- The successor strict bound adds exactly the groups of rank `n`. -/
theorem rationalStrictlyLowerRankFourierInjectivity_succ_iff {n : ℕ} :
    RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} (n + 1) ↔
      RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n ∧
        RationalExactRankFourierInjectivityStatement.{u, uV} n := by
  constructor
  · intro h
    refine ⟨rationalStrictlyLowerRankFourierInjectivity_mono (Nat.le_succ n) h, ?_⟩
    intro F _ _ _ _ G _ _ hG S i hi hrank
    exact h F G hG S i hi (Nat.lt_succ_iff_lt_or_eq.mpr (Or.inr hrank))
  · rintro ⟨hlower, hexact⟩ F _ _ _ _ G _ _ hG S i hi hrank
    rcases Nat.lt_succ_iff_lt_or_eq.mp hrank with hlt | heq
    · exact hlower F G hG S i hi hlt
    · exact hexact F G hG S i hi heq

/-- Advance orbit finiteness first at rank `n`. Then advance injectivity
using finiteness through rank `n` and injectivity on strictly lower ranks. -/
theorem rationalPlancherelRankInduction
    (finiteStep : ∀ n : ℕ, 0 < n →
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n →
      RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n →
      RationalExactRankDiscreteSeriesOrbitFinitenessStatement.{u, uV} n)
    (injectiveStep : ∀ n : ℕ,
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (n + 1) →
      RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n →
      RationalExactRankFourierInjectivityStatement.{u, uV} n) :
    RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV} ∧
      RationalFourierInjectivityGlobalStatement.{u, uV} := by
  have hbounds (n : ℕ) :
      RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} n ∧
        RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n := by
    induction n with
    | zero =>
      exact ⟨rationalStrictlyLowerRankOrbitFiniteness_zero,
        rationalStrictlyLowerRankFourierInjectivity_zero⟩
    | succ n ih =>
      have hexact : RationalExactRankDiscreteSeriesOrbitFinitenessStatement.{u, uV} n := by
        cases n with
        | zero => exact rationalRankZeroDiscreteSeriesOrbitFiniteness
        | succ m => exact finiteStep (m + 1) (Nat.zero_lt_succ m) ih.1 ih.2
      have hfinite := rationalStrictlyLowerRankOrbitFiniteness_succ_iff.mpr ⟨ih.1, hexact⟩
      exact ⟨hfinite,
        rationalStrictlyLowerRankFourierInjectivity_succ_iff.mpr
          ⟨ih.2, injectiveStep n hfinite ih.2⟩⟩
  exact ⟨rationalDiscreteSeriesOrbitFiniteness_iff_all_rank_bounds.mpr fun n => (hbounds n).1,
    rationalFourierInjectivityGlobal_iff_all_rank_bounds.mpr fun n => (hbounds n).2⟩

section ProperLevi

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean
  RationalSemistandardLeviFourierData.ambientHaar_haar
  RationalSemistandardLeviFourierData.ambientHaar_right
  RationalSemistandardLeviFourierData.centerNormal
  RationalSemistandardLeviFourierData.quotientMeasurable
  RationalSemistandardLeviFourierData.quotientBorel
  RationalSemistandardLeviFourierData.quotientHaar_haar
  RationalSemistandardLeviFourierData.quotientHaar_inv

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {nu : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)} {hKc : IsCompact (K : Set (rationalPoints G))}
  {hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup}
  {N : ℕ} [Nonempty (Fin N)] {rho : MatrixRepresentation G (Fin N)}
  {muG : Measure (rationalPoints G)}
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  {a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme}
  {ha : ∀ t, IsSplitComponent (a t)}
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  {mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t))}
  [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
  {d : ∀ t : SemistandardSpectralIndex i, CompactData t}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Strictly lower rank Fourier injectivity supplies the zero case for
each actual proper-Levi Fourier family used in VIII.2.1. -/
theorem RationalSemistandardLeviFourierData.fourier_injective_of_lowerRank
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hp : p.IsProper)
    (hlower : RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} (relativeRootRank i))
    (c : RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha mu d p) :
    Function.Injective c.fourier := by
  let := c.model.reductive.isAffineHom
  let : IsAffine c.model.scheme.X.left := isAffine_of_isAffineHom c.model.scheme.X.hom
  let := c.model.reductive.smooth
  have hlocal := hlower F c.model.scheme c.model.reductive c.torus c.iM c.maximal (c.rank_lt hG hi hp)
  have hzero := hlocal c.model.reductive c.torus c.iM c.maximal c.nuM c.generic
    c.compact c.compact_isCompact c.iwasawa N (rho.restrict c.model.inclusion)
    c.ambientHaar c.squareIntegrableWeight c.splitCenterTorus c.splitCenterInclusion
    c.splitComponent c.quotientHaar c.compactData c.normalization c.tempered
  exact (injective_iff_map_eq_zero c.fourier).mpr hzero

end ProperLevi

end Langlands.HarishChandraSchwartz
