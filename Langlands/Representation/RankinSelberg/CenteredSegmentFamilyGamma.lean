import Langlands.Representation.RankinSelberg.CenteredSegmentFamilyDualLProduct
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Global.Factors.AppendixPoleCountingProof

/-! # Actual gamma germs and rigidity of centered segment families -/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial Classification LocalFactor

universe uF uV uI

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance centeredGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable {I : Type uI} {n : I → ℕ}
  {δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
  (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (n i) (δ i))

/-- The actual rational spectral value has the Appendix gamma germ at every
complex point. No equality of the two values at a displayed pole is required. -/
def IsCenteredSegmentFamilyGammaGerm [Fintype I]
    (s : I → ℝ) (G : RatFunc ℂ) (base : I → I → ℂ → ℂ)
    (epsilon : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, rationalSpectralValue F.canonicalTopologicalData.residueCardinality G
    =ᶠ[𝓝[≠] z]
      Global.PoleComparison.blockGamma (fun i => (d i).segment.length - 1) s base epsilon

/-- The two actual L-products identify the polynomial gamma expression as
an ordinary complex function, with totalized inverses. -/
theorem IsCenteredSegmentFamilyLProductPair.polynomialGammaExpression_eq [Fintype I]
    {s : I → ℝ} {P Pd : ℂ[X]} {base : I → I → ℂ → ℂ}
    (h : IsCenteredSegmentFamilyLProductPair F d s P Pd base)
    (c : ℂˣ) (m : ℤ) :
    polynomialGammaExpression F.canonicalTopologicalData.residueCardinality c m P Pd =
      Global.PoleComparison.blockGamma (fun i => (d i).segment.length - 1) s base
        (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m) := by
  exact IsCenteredSegmentFamilyLProductPair.gammaExpression F d h
    (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m)

/-- Combine the actual rational formula with the two L-products only on
punctured neighborhoods, so cancellation at polynomial zeros is respected. -/
theorem IsCenteredSegmentFamilyLProductPair.gammaGerm [Fintype I]
    {s : I → ℝ} {P Pd : ℂ[X]} {base : I → I → ℂ → ℂ}
    (h : IsCenteredSegmentFamilyLProductPair F d s P Pd base)
    (c : ℂˣ) (m : ℤ) {G : RatFunc ℂ}
    (hG : G = rationalGammaExpression (residueReflection F) c m P Pd)
    (hPd : Pd ≠ 0) :
    IsCenteredSegmentFamilyGammaGerm F d s G base
      (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m) := by
  intro z
  rw [hG]
  have hg := rationalSpectralValue_eventuallyEq_polynomialGammaExpression
    F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one (residueReflection F) c
    (coe_residueReflection F) m P Pd hPd z
  rw [IsCenteredSegmentFamilyLProductPair.polynomialGammaExpression_eq F d h c m] at hg
  exact hg

/-- Orders depend on the punctured germ, including at cancelled singularities. -/
theorem IsCenteredSegmentFamilyGammaGerm.order_eq [Fintype I]
    {s : I → ℝ} {G : RatFunc ℂ} {base : I → I → ℂ → ℂ} {epsilon : ℂ → ℂ}
    (h : IsCenteredSegmentFamilyGammaGerm F d s G base epsilon) (z : ℂ) :
    meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) z =
      meromorphicOrderAt
        (Global.PoleComparison.blockGamma (fun i => (d i).segment.length - 1)
          s base epsilon) z :=
  meromorphicOrderAt_congr (h z)

/-- The canonical epsilon monomial supplies a holomorphic unit everywhere. -/
theorem epsilonMonomial_holomorphicUnitAt (c : ℂˣ) (m : ℤ) (z : ℂ) :
    Global.PoleComparison.HolomorphicUnitAt
      (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m) z := by
  have hq : 0 < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast Nat.zero_lt_one.trans
      F.canonicalTopologicalData.residueCardinality_gt_one
  exact ⟨LocalFactor.epsilonMonomial_analyticAt _ hq c m z,
    epsilonMonomial_ne_zero _ hq c m z⟩

/-- Numerical Appendix rigidity applies to the actual gamma germ once its
real positive orders are confined to zero. -/
theorem IsCenteredSegmentFamilyGammaGerm.segmentRigidity [Fintype I] [Nonempty I]
    {s : I → ℝ} {G : RatFunc ℂ} {base : I → I → ℂ → ℂ} {epsilon : ℂ → ℂ}
    (h : IsCenteredSegmentFamilyGammaGerm F d s G base epsilon)
    (partner : I → I)
    (hs : Global.PoleComparison.SymmetricBlockData
      (fun i => (d i).segment.length - 1) s partner)
    (hb : Global.PoleComparison.BasePairConditions partner base)
    (heps : ∀ t : ℝ, Global.PoleComparison.HolomorphicUnitAt epsilon (t : ℂ))
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0) :
    ∀ i, (d i).segment.length = 1 ∧ s i = 0 := by
  have hr := Global.PoleComparison.appendixBlockRigidity I
    (fun i => (d i).segment.length - 1) s partner base epsilon hs hb heps
    (fun t ht => hzero t (by
      rwa [IsCenteredSegmentFamilyGammaGerm.order_eq F d h (t : ℂ)]))
  intro i
  have hi := hr i
  have hpos := (d i).segment.length_pos
  exact ⟨by omega, hi.2⟩

/-- For the actual centered bases of a unitary generic datum, the supplied
rational formula and two L-products reduce the order constraint to rigidity. -/
theorem centeredSegmentFamily_rigidity_of_unitaryGenericDatum
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    {N : ℕ} {B : BlockShape N} [Nonempty (Fin B.length)]
    {δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    {s : Fin B.length → ℝ}
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i))
    (hU : IsUnitaryGenericDatum F F.canonicalTopologicalData B δ s)
    {P Pd : ℂ[X]}
    (hL : IsCenteredSegmentFamilyLProductPair F d s P Pd
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal))
    (c : ℂˣ) (m : ℤ) {G : RatFunc ℂ}
    (hG : G = rationalGammaExpression (residueReflection F) c m P Pd)
    (hPd : Pd ≠ 0)
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0) :
    ∀ i, (d i).segment.length = 1 ∧ s i = 0 := by
  obtain ⟨partner, hs, _, hb⟩ :=
    exists_symmetric_centeredSegmentBaseEulerFamily hEq ψ ν hU d
  exact IsCenteredSegmentFamilyGammaGerm.segmentRigidity F d
    (IsCenteredSegmentFamilyLProductPair.gammaGerm F d hL c m hG hPd)
    partner hs hb (fun t => epsilonMonomial_holomorphicUnitAt F c m (t : ℂ)) hzero

end Langlands.RankinSelberg
