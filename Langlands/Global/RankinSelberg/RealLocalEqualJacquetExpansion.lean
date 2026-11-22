import Langlands.Global.RankinSelberg.RealLocalEqualNormalizedFactors
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.RankinSelberg.RealParameterDeterminant
import Langlands.Global.RankinSelberg.RealUniformContinuationReduction

/-! # The real equal-rank equation from the matched expansion in Jacquet §8.2 -/

noncomputable section

open Filter MeasureTheory
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := borel _
local instance (r : ℕ) : BorelSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

/-- The multiplied-out equation for a pair of meromorphic continuations, with the inverse
block lists and the positive self-dual scale at the indicated epsilon parameter. -/
def PairMeromorphicIdentity (ds es : List RealBlock) (b : ℝˣ) (sign : ℂ)
    (M Md : ℂ → ℂ) : Prop :=
  ∀ᶠ s in codiscrete ℂ,
    ((realPairLFactor ds es).denominator s)⁻¹ * Md (1 - s) =
      sign * (realPairEpsilon ds es b (NNReal.sqrt ‖(b : ℝ)‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s : ℂ) *
      ((realPairLFactor (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock)).denominator (1 - s))⁻¹ * M s

/-- Multiply the adjacent and matrix equations term by term, including the Weyl sign
of the dual expansion and the epsilon sign change in the adjacent equation. -/
theorem pairMeromorphicIdentity_equal_sum_products {r k : ℕ} (d : RealCharacterData)
    (ds es : List RealBlock) (hd : realRank ds = r + 1) (he : realRank es = r + 2)
    (a : ℝˣ) (A Ad Z Zd : Fin k → ℂ → ℂ)
    (hA : ∀ i, PairMeromorphicIdentity es ds a
      ((determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ)) (A i) (Ad i))
    (hZ : ∀ i, PairMeromorphicIdentity [.character d] es (-a) 1 (Z i) (Zd i)) :
    PairMeromorphicIdentity (.character d :: ds) es (-a)
      ((determinant (.character d :: ds) (-1) : ℂ) ^ (r + 1))
      (fun s => ∑ i, A i s * Z i s)
      (fun s => (d.character (-1) : ℂ) ^ (r + 1) * ∑ i, Ad i s * Zd i s) := by
  unfold PairMeromorphicIdentity at hA hZ ⊢
  filter_upwards [eventually_all.mpr hA, eventually_all.mpr hZ] with s hsA hsZ
  simp only [List.map_cons, realPairLFactor_cons_mul (.character d) ds es,
    realPairLFactor_cons_mul (RealLocalJacquet.dualBlock (.character d))
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock),
    ReciprocalEntire.denominator_mul, mul_inv, mul_assoc, Finset.mul_sum,
    Units.val_neg, nnnorm_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha := hsA i
  rw [CuspidalPairPartialGammaGlobal.realPairLFactor_denominator_comm es ds,
    CuspidalPairPartialGammaGlobal.realPairLFactor_denominator_comm
      (es.map RealLocalJacquet.dualBlock) (ds.map RealLocalJacquet.dualBlock),
    CuspidalPairPartialGammaGlobal.realPairEpsilon_comm es ds] at ha
  have hz := hsZ i
  simp only [one_mul, Units.val_neg, nnnorm_neg] at hz
  let c := NNReal.sqrt ‖(a : ℝ)‖₊
  have hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  let L (xs ys : List RealBlock) := ((realPairLFactor xs ys).denominator s)⁻¹
  let Ld (xs ys : List RealBlock) := ((realPairLFactor (xs.map RealLocalJacquet.dualBlock)
    (ys.map RealLocalJacquet.dualBlock)).denominator (1 - s))⁻¹
  let E (xs ys : List RealBlock) (b : ℝˣ) := (realPairEpsilon xs ys b c hc s : ℂ)
  let u := (d.character (-1) : ℂ) ^ (r + 1)
  let v := (determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ)
  change L [.character d] es * (L ds es * (u * (Ad i (1 - s) * Zd i (1 - s)))) =
    (determinant (.character d :: ds) (-1) : ℂ) ^ (r + 1) *
      (E (.character d :: ds) es (-a) * (Ld [.character d] es * (Ld ds es * (A i s * Z i s))))
  change L ds es * Ad i (1 - s) = v * E ds es a * Ld ds es * A i s at ha
  change L [.character d] es * Zd i (1 - s) = E [.character d] es (-a) * Ld [.character d] es * Z i s at hz
  calc
    _ = u * ((L ds es * Ad i (1 - s)) * (L [.character d] es * Zd i (1 - s))) := by ring
    _ = (u * ((v * E ds es a) * E [.character d] es (-a))) *
          (Ld [.character d] es * (Ld ds es * (A i s * Z i s))) := by rw [ha, hz]; ring
    _ = _ := by rw [equal_epsilon_coefficient d ds es hd he a c hc s]; ring

/-- The adjacent-rank continuation input, restricted to indices `r+1` and `r`. -/
def AdjacentContinuationAtRank (r : ℕ) : Prop :=
  ∀ (es ds : List RealBlock), realRank es = r + 2 → realRank ds = r + 1 →
  ∀ (b : ℝˣ) (D : RealQuotientMeasureData r)
    (V : Langlands.GeneralLinear (r + 2) ℝ → ℂ)
    (U : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    V ∈ realUniformWhittakerModel (r + 1) es b → U ∈ realUniformWhittakerModel r ds (-b) →
    UnequalContinuation (Nat.lt_succ_self r) b D V U es ds
      (es.map RealLocalJacquet.dualBlock) (ds.map RealLocalJacquet.dualBlock) (-b)
      ((determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ))

/-- A pair of half-plane identities of the form of the §8.2 expansion. Each summand
uses continuations of a matrix integral and its dual and an adjacent-rank pair of
Whittaker coefficients. The adjacent data may vary with the summand. -/
def HasEqualJacquetExpansion {r : ℕ} (d : RealCharacterData) (ds es : List RealBlock)
    (a : ℝˣ) (D : RealQuotientMeasureData (r + 1))
    (W V : Langlands.GeneralLinear (r + 2) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 2) → ℝ) ℂ) : Prop :=
  ∃ (k : ℕ) (D₁ : Fin k → RealQuotientMeasureData r)
    (U₁ : Fin k → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (V₁ : Fin k → Langlands.GeneralLinear (r + 2) ℝ → ℂ) (Z Zd : Fin k → ℂ → ℂ),
    (∀ i, U₁ i ∈ realUniformWhittakerModel r ds a ∧
      V₁ i ∈ realUniformWhittakerModel (r + 1) es (-a) ∧
      MeromorphicOn (Z i) Set.univ ∧ MeromorphicOn (Zd i) Set.univ ∧
      PairMeromorphicIdentity [.character d] es (-a) 1 (Z i) (Zd i)) ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realEqualIntegral D W V Φ s =
        ∑ i, realUnequalIntegral (Nat.lt_succ_self r) (D₁ i) (V₁ i) (U₁ i) s * Z i s ∧
      realEqualDualIntegral (-a) D W V Φ s =
        (d.character (-1) : ℂ) ^ (r + 1) *
          ∑ i, realUnequalDualIntegral (Nat.lt_succ_self r) (-a) (D₁ i) (V₁ i) (U₁ i) s * Zd i s

/-- The §8.2 continuation step, conditional on the adjacent-rank equation and a matched
finite expansion of the actual equal-rank integrals. -/
def RealLocalEqualJacquetExpansionReductionStatement : Prop :=
  ∀ (r : ℕ) (d : RealCharacterData) (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = r + 2 → AdjacentContinuationAtRank r →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData (r + 1))
    (W V : Langlands.GeneralLinear (r + 2) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 2) → ℝ) ℂ),
    HasEqualJacquetExpansion d ds es a D W V Φ →
    EqualContinuation a (-a) D W V Φ (.character d :: ds) es
      ((.character d :: ds).map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock)
      ((determinant (.character d :: ds) (-1) : ℂ) ^ (r + 1))

theorem realLocalEqualJacquetExpansionReduction : RealLocalEqualJacquetExpansionReductionStatement := by
  intro r d ds es hd he hAdjacent a D W V Φ hExpansion
  obtain ⟨k, D₁, U₁, V₁, Z, Zd, hZ, τ, hτ⟩ := hExpansion
  have ht (i : Fin k) :
      ∃ (ρ : ℝ) (A Ad : ℂ → ℂ), MeromorphicOn A Set.univ ∧ MeromorphicOn Ad Set.univ ∧
        (∀ s : ℂ, ρ < s.re →
          realUnequalIntegral (Nat.lt_succ_self r) (D₁ i) (V₁ i) (U₁ i) s = A s ∧
          realUnequalDualIntegral (Nat.lt_succ_self r) (-a) (D₁ i) (V₁ i) (U₁ i) s = Ad s) ∧
        PairMeromorphicIdentity es ds a
          ((determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ)) A Ad := by
    obtain ⟨ρ, A, Ad, hA, hAd, hI, hId, hFE⟩ :=
      hAdjacent es ds he hd (-a) (D₁ i) (V₁ i) (U₁ i) (hZ i).2.1
        (by simpa only [neg_neg] using (hZ i).1)
    refine ⟨ρ, A, Ad, hA, hAd, fun s hs => ⟨hI s hs, hId s hs⟩, ?_⟩
    simpa only [PairMeromorphicIdentity, neg_neg, Units.val_neg, nnnorm_neg] using hFE
  choose ρ A Ad hA hAd hright hFE using ht
  obtain ⟨β, hβ⟩ := (Set.finite_range ρ).bddAbove
  let b := max τ β
  let M := fun s => ∑ i, A i s * Z i s
  let Md := fun s => (d.character (-1) : ℂ) ^ (r + 1) * ∑ i, Ad i s * Zd i s
  have hmer : MeromorphicOn M Set.univ :=
    MeromorphicOn.fun_sum fun i _ => (hA i).mul (hZ i).2.2.1
  have hmerd : MeromorphicOn Md Set.univ := by
    change MeromorphicOn ((fun _ : ℂ => (d.character (-1) : ℂ) ^ (r + 1)) *
      (fun s => ∑ i, Ad i s * Zd i s)) Set.univ
    exact (MeromorphicOn.const _).mul (MeromorphicOn.fun_sum fun i _ => (hAd i).mul (hZ i).2.2.2.1)
  refine ⟨b, M, Md, hmer, hmerd, ?_, ?_, ?_⟩
  · intro s hs
    change realEqualIntegral D W V Φ s = M s
    rw [(hτ s ((le_max_left _ _).trans_lt hs)).1]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hright i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_right _ _).trans_lt hs))).1]
  · intro s hs
    change realEqualDualIntegral (-a) D W V Φ s = Md s
    rw [(hτ s ((le_max_left _ _).trans_lt hs)).2]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hright i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_right _ _).trans_lt hs))).2]
  · simpa only [PairMeromorphicIdentity, Units.val_neg, nnnorm_neg] using
      pairMeromorphicIdentity_equal_sum_products d ds es hd he a A Ad Z Zd hFE fun i => (hZ i).2.2.2.2

end Langlands.Global.RankinSelbergGlobal.RealJacquet
