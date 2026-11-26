import Langlands.Global.RankinSelberg.RealPlaceAscendingPrincipalSeriesReduction
import Langlands.Global.RankinSelberg.RealBlockFamilyNormalization
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Global.RankinSelberg.RealPositionFamilyContinuation
import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient
import Langlands.Global.RankinSelberg.RealTemperedBlockConvergence
import Langlands.Global.RankinSelberg.RealTemperedWhittakerBound
import Langlands.Global.RankinSelberg.RealUnequalCanonicalReflection
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth

/-! # Real block continuation from character growth and tempered families -/

noncomputable section

open Metric Set Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open ArchimedeanLocal RealJacquet RealPrincipalSeries RealTemperedWhittaker
open RealUnequalFamily (blockExponent blockShape eq_blockList)

private def shapes (ds : List RealBlock) (i : Fin ds.length) : Shape := blockShape ds[i]

private def exponents (ds : List RealBlock) (z : ℂ) (i : Fin ds.length) : ℂ :=
  (blockExponent ds[i]).re * z + (blockExponent ds[i]).im * Complex.I

/-- Vary the real parts affinely while keeping the block shapes and initial imaginary parts. -/
def deformBlocks (ds : List RealBlock) (z : ℂ) : List RealBlock :=
  blockList (shapes ds) (exponents ds z)

private theorem differentiable_exponents (ds : List RealBlock) : Differentiable ℂ (exponents ds) :=
  differentiable_pi.mpr fun _ => (differentiable_id.const_mul _).add_const _

@[simp] theorem deformBlocks_one (ds : List RealBlock) : deformBlocks ds 1 = ds := by
  unfold deformBlocks
  conv_rhs => rw [eq_blockList ds]
  congr 1
  funext i
  apply Complex.ext <;> simp [exponents]

private theorem map_deformBlocks_eq {A : Type*} (f : RealBlock → A)
    (hf : ∀ sh u v, f (blockOfParams sh u) = f (blockOfParams sh v)) (ds : List RealBlock) (z : ℂ) :
    (deformBlocks ds z).map f = ds.map f := by
  calc
    _ = (deformBlocks ds 1).map f := by
      simp only [deformBlocks, blockList, List.map_ofFn]
      congr 1
      funext i
      exact hf (shapes ds i) _ _
    _ = _ := by rw [deformBlocks_one]

@[simp] theorem realRank_deformBlocks (ds : List RealBlock) (z : ℂ) :
    realRank (deformBlocks ds z) = realRank ds := by
  unfold realRank
  rw [map_deformBlocks_eq _ (by rintro (p | l) u v <;> rfl)]

private theorem determinant_deformBlocks (ds : List RealBlock) (z : ℂ) :
    determinant (deformBlocks ds z) (-1) = determinant ds (-1) := by
  unfold determinant
  rw [map_deformBlocks_eq]
  rintro (p | l) u v <;> apply Units.ext
  · simp [blockOfParams, RealBlock.determinant, RealCharacterData.character_eq]
  · simp [blockOfParams, RealBlock.determinant, ComplexCharacterData.coe_realInducedDeterminant,
      ComplexCharacterData.character_eq, realToComplex, characterOfParams_weight]

private theorem realBlockExponent_deformBlocks {ds : List RealBlock} {z : ℂ} (hz : z.re = 0) :
    ∀ d ∈ deformBlocks ds z, realBlockExponent d = 0 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  cases shapes ds i <;>
    simp [blockOfParams, realBlockExponent, exponents, Complex.mul_re, hz]

local notation "G" => fun r : ℕ => Langlands.GeneralLinear (r + 1) ℝ

/-- A pair of coefficients at the endpoint extends along the block exponent deformation
with a jointly holomorphic right-half-plane zeta integral. -/
def HasRealOrdinaryHolomorphicTestFamily {r t : ℕ} (ds es : List RealBlock) (a : ℝˣ)
    (I : (G r → ℂ) → (G t → ℂ) → ℂ → ℂ) (W : G r → ℂ) (V : G t → ℂ) : Prop :=
  ∃ (U : ℂ → G r → ℂ) (U' : ℂ → G t → ℂ) (σ : ℝ), U 1 = W ∧ U' 1 = V ∧
    (∀ z ∈ ball 0 3, U z ∈ realWhittakerModel r (deformBlocks ds z) a ∧
      U' z ∈ realWhittakerModel t (deformBlocks es z) (-a)) ∧
    DifferentiableOn ℂ (fun u : ℂ × ℂ => I (U u.1) (U' u.1) u.2)
      (ball 0 3 ×ˢ {s : ℂ | σ < s.re})

/-- The family condition for all the real ordinary unequal-rank and positive-index
equal-rank tests, with the additive parameter, quotient measure and Schwartz test fixed. -/
def RealOrdinaryHolomorphicTestFamiliesStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = t + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData t) (W : G r → ℂ) (V : G t → ℂ),
      W ∈ realWhittakerModel r ds a → V ∈ realWhittakerModel t es (-a) →
      HasRealOrdinaryHolomorphicTestFamily ds es a (realUnequalIntegral h D) W V) ∧
  ∀ (r : ℕ), 0 < r → ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r) (W V : G r → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      W ∈ realWhittakerModel r ds a → V ∈ realWhittakerModel r es (-a) →
      HasRealOrdinaryHolomorphicTestFamily ds es a (fun W V => realEqualIntegral D W V Φ) W V

private theorem mem_ascendingExpand {r : ℕ} {ds : List RealBlock} {a : ℝˣ} {W : G r → ℂ}
    (hr : realRank ds = r + 1) (hW : W ∈ realWhittakerModel r ds a) :
    W ∈ realUniformWhittakerModel r (ascendingExpand ds) a :=
  uniformModel_le_ascendingExpand r ds hr a (realWhittakerModels_eq r ds hr a ▸ hW)

private def PositionNormalization (ds es : List RealBlock) (Z : ℂ → ℂ) : Prop :=
  Nonempty (OrdinaryIntegralNormalization Z
    (fun s => ((realPairLFactor (expand ds) (expand es)).denominator s)⁻¹))

private def BlockPackage (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c)
    (sign : ℂ) (Z Zd : ℂ → ℂ) : Prop :=
  ContinuationPackage Z Zd (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((realPairLFactor (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
    (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign

private theorem normalizations_of_ascending {ds es : List RealBlock} {b : ℝˣ} {c : ℝ≥0} {hc : 0 < c}
    {sign : ℂ} {Z Zd : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth (ascendingExpand ds) (ascendingExpand es)
      ((ascendingExpand ds).map RealLocalJacquet.dualBlock)
      ((ascendingExpand es).map RealLocalJacquet.dualBlock) b c hc sign Z Zd) :
    PositionNormalization ds es Z ∧ BlockPackage ds es b c hc sign Z Zd := by
  have hp := ascendingExpand_perm ds
  have hq := ascendingExpand_perm es
  have hd := realPairLFactor_perm hp hq
  have hdd := realPairLFactor_perm (hp.map RealLocalJacquet.dualBlock) (hq.map RealLocalJacquet.dualBlock)
  have h' : HasRealPairNormalizedGrowth (expand ds) (expand es)
      ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock)
      b c hc sign Z Zd := by
    simpa only [HasRealPairNormalizedGrowth, hd, hdd, realPairEpsilon_perm hp hq] using h
  refine ⟨?_, continuationPackage_of_expand ds es b c hc h'.continuationPackage⟩
  obtain ⟨N, _, hN, _, _, _, ⟨σ, hσ⟩, _⟩ := h'
  let L := realPairLFactor (expand ds) (expand es)
  obtain ⟨τ, hτ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks (expand ds) (expand es))
  refine ⟨⟨N, fun s _ => hN.analyticAt s, ⟨max σ τ, fun s hs => ?_⟩⟩⟩
  change Z s = N s * (L.denominator s)⁻¹
  have hd₀ : L.denominator s ≠ 0 := hτ s ((le_max_right _ _).trans_lt hs)
  rw [(hσ s ((le_max_left _ _).trans_lt hs)).1]
  change _ = (L.denominator s * Z s) * (L.denominator s)⁻¹
  rw [mul_comm (L.denominator s) (Z s), mul_assoc, mul_inv_cancel₀ hd₀, mul_one]

private theorem regular_and_gauge {r : ℕ} {ds : List RealBlock} {z : ℂ} {a : ℝˣ}
    {W : G r → ℂ} (hBound : ∀ i : ℕ, 0 < i → RealTemperedWhittakerBoundAtRank i)
    (hr : realRank ds = r + 1) (hz : z.re = 0) (hW : W ∈ realWhittakerModel r (deformBlocks ds z) a) :
    W ∈ RealLocalWhittaker.regularFunctions r a ∧ HasTemperedGauge W := by
  have hR := realLocalWhittakerRegularity r (deformBlocks ds z) a W hW
  have hB : RealTemperedWhittakerBoundAtRank r := by
    cases r with
    | zero => exact realTemperedWhittakerBoundAtRank_zero
    | succ r => exact hBound (r + 1) (Nat.succ_pos _)
  exact ⟨hR [], hasTemperedGauge_of_derivativeBound hR
    (hasTemperedDerivativeBound_of_model hB ((realRank_deformBlocks ds z).trans hr)
      (realBlockExponent_deformBlocks hz) hW)⟩

private theorem normalization_at_one (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c)
    (sign : ℂ) (hSign : sign ≠ 0) (Z Zd : ℂ × ℂ → ℂ) (σ : ℝ)
    (hZ : DifferentiableOn ℂ Z (ball 0 3 ×ˢ {s : ℂ | σ < s.re}))
    (hNorm : ∀ z ∈ ball 0 3,
      PositionNormalization (deformBlocks ds z) (deformBlocks es z) (fun s => Z (z, s)))
    (hInit : ∀ z ∈ ball 0 3, z.re = 0 →
      DifferentiableOn ℂ (fun s => Z (z, s)) {s : ℂ | 0 < s.re} ∧
      DifferentiableOn ℂ (fun s => Zd (z, s)) {s : ℂ | 0 < s.re} ∧
      BlockPackage (deformBlocks ds z) (deformBlocks es z) b c hc sign
        (fun s => Z (z, s)) (fun s => Zd (z, s))) :
    Nonempty (OrdinaryIntegralNormalization (fun s => Z (1, s))
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹)) := by
  have hd := differentiable_exponents ds
  have he := differentiable_exponents es
  obtain ⟨F, hF, htrace⟩ := realPositionFamilyContinuation
    (shapes ds) (shapes es) (exponents ds) (exponents es) hd he Z σ hZ
    ⟨3, by norm_num, hNorm⟩
  have hResult := realBlockFamilyNormalization (3 / 2) (by norm_num)
    (shapes ds) (shapes es) (exponents ds) (exponents es) b c hc sign hd he hSign
    F Z Zd hF (fun z hz => ⟨σ, htrace z hz⟩)
    (fun z hz => hInit z (ball_subset_ball (by norm_num) hz))
  have hOne : (1 : ℂ) ∈ ball 0 (3 / 2) := by norm_num [mem_ball, dist_zero_right]
  have hAtOne : Nonempty (OrdinaryIntegralNormalization (fun s => Z (1, s))
      (fun s => ((realPairLFactor (deformBlocks ds 1) (deformBlocks es 1)).denominator s)⁻¹)) :=
    hResult 1 hOne
  simpa only [deformBlocks_one] using hAtOne

/-- The real ordinary continuation follows from normalized growth for character pairs,
the tempered scalar Whittaker bound, and the holomorphic deformation of the exact tests. -/
def RealOrdinaryBlockAssemblyStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r), RealLocalUnequalCharacterGrowthAtRanks r t h) →
    (∀ r : ℕ, 0 < r → RealLocalEqualCharacterGrowthAtRank r) →
    (∀ r : ℕ, 0 < r → RealTemperedWhittakerBoundAtRank r) →
    RealOrdinaryHolomorphicTestFamiliesStatement →
    RealOrdinaryNormalizedContinuationStatement

set_option maxHeartbeats 1200000 in
theorem realOrdinaryBlockAssembly : RealOrdinaryBlockAssemblyStatement := by
  intro hUnequal hEqual hBound hFamilies
  constructor
  · rintro r t h ds es hr ht a D ⟨W, V⟩
    obtain ⟨U, U', σ, hU, hU', hModel, hHol⟩ := hFamilies.1 r t h ds es hr ht a D W V W.2 V.2
    let c := NNReal.sqrt ‖(a : ℝ)‖₊
    have hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
    let sign := (determinant ds (-1) : ℂ) ^ (t + 1) * (determinant es (-1) : ℂ)
    have hSign : sign ≠ 0 := mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)
    let Z (u : ℂ × ℂ) := realUnequalIntegral h D (U u.1) (U' u.1) u.2
    let Zd (u : ℂ × ℂ) := realUnequalDualIntegral h a D (U u.1) (U' u.1) u.2
    have hSlice (z : ℂ) (hz : z ∈ ball 0 3) :
        PositionNormalization (deformBlocks ds z) (deformBlocks es z) (fun s => Z (z, s)) ∧
        BlockPackage (deformBlocks ds z) (deformBlocks es z) (-a) c hc sign
          (fun s => Z (z, s)) (fun s => Zd (z, s)) := by
      have hd := (realRank_deformBlocks ds z).trans hr
      have he := (realRank_deformBlocks es z).trans ht
      have hN := hUnequal r t h (ascendingExpand (deformBlocks ds z)) (ascendingExpand (deformBlocks es z))
        ⟨_, rfl⟩ ⟨_, rfl⟩ ((realRank_ascendingExpand _).trans hd) ((realRank_ascendingExpand _).trans he)
        a D (U z) (U' z) (mem_ascendingExpand hd (hModel z hz).1) (mem_ascendingExpand he (hModel z hz).2)
      rw [RealPrincipalSeries.determinant_ascendingExpand, RealPrincipalSeries.determinant_ascendingExpand,
        determinant_deformBlocks, determinant_deformBlocks] at hN
      exact normalizations_of_ascending hN
    change Nonempty (OrdinaryIntegralNormalization (realUnequalIntegral h D (W : G r → ℂ) V)
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹))
    rw [← hU, ← hU']
    refine normalization_at_one ds es (-a) c hc sign hSign Z Zd σ hHol
      (fun z hz => (hSlice z hz).1) ?_
    intro z hz him
    obtain ⟨hW, hWg⟩ := regular_and_gauge hBound hr him (hModel z hz).1
    obtain ⟨hV, hVg⟩ := regular_and_gauge hBound ht him (hModel z hz).2
    exact ⟨(realTemperedOrdinaryConvergence.1 r t h D a _ _ hW hV hWg hVg).2,
      (realTemperedBlockConvergence r t h D a _ _ hW hV hWg hVg).2, (hSlice z hz).2⟩
  · intro r
    cases r with
    | zero =>
      exact fun ds es hr ht a D => (rankOneOrdinaryNormalizedTests.1 ds es hr ht a D).1
    | succ k =>
      rintro ds es hr ht a D ⟨W, V, Φ⟩
      let r := k + 1
      have hp : 0 < r := Nat.succ_pos k
      obtain ⟨U, U', σ, hU, hU', hModel, hHol⟩ :=
        hFamilies.2 r hp ds es hr ht a D W V Φ W.2 V.2
      let c := NNReal.sqrt ‖(a : ℝ)‖₊
      have hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
      let sign := (determinant ds (-1) : ℂ) ^ r
      have hSign : sign ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
      let Z (u : ℂ × ℂ) := realEqualIntegral D (U u.1) (U' u.1) Φ u.2
      let Zd (u : ℂ × ℂ) := realEqualDualIntegral (-a) D (U u.1) (U' u.1) Φ u.2
      have hSlice (z : ℂ) (hz : z ∈ ball 0 3) :
          PositionNormalization (deformBlocks ds z) (deformBlocks es z) (fun s => Z (z, s)) ∧
          BlockPackage (deformBlocks ds z) (deformBlocks es z) (-a) c hc sign
            (fun s => Z (z, s)) (fun s => Zd (z, s)) := by
        have hd := (realRank_deformBlocks ds z).trans hr
        have he := (realRank_deformBlocks es z).trans ht
        have hN := hEqual r hp (ascendingExpand (deformBlocks ds z)) (ascendingExpand (deformBlocks es z))
          ⟨_, rfl⟩ ⟨_, rfl⟩ ((realRank_ascendingExpand _).trans hd) ((realRank_ascendingExpand _).trans he)
          a D (U z) (U' z) Φ (mem_ascendingExpand hd (hModel z hz).1) (mem_ascendingExpand he (hModel z hz).2)
        rw [RealPrincipalSeries.determinant_ascendingExpand, determinant_deformBlocks] at hN
        exact normalizations_of_ascending hN
      change Nonempty (OrdinaryIntegralNormalization (realEqualIntegral D (W : G r → ℂ) V Φ)
        (fun s => ((realPairLFactor ds es).denominator s)⁻¹))
      rw [← hU, ← hU']
      refine normalization_at_one ds es (-a) c hc sign hSign Z Zd σ hHol
        (fun z hz => (hSlice z hz).1) ?_
      intro z hz him
      obtain ⟨hW, hWg⟩ := regular_and_gauge hBound hr him (hModel z hz).1
      obtain ⟨hV, hVg⟩ := regular_and_gauge hBound ht him (hModel z hz).2
      exact ⟨(realTemperedOrdinaryConvergence.2 r D a (-a) _ _ Φ hW hV hWg hVg).2.1,
        (realTemperedOrdinaryConvergence.2 r D a (-a) _ _ Φ hW hV hWg hVg).2.2, (hSlice z hz).2⟩

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
