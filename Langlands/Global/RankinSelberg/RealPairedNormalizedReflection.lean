import Langlands.Global.RankinSelberg.RealOrdinaryEqualCharacterContinuation
import Langlands.Global.RankinSelberg.RealPairedOrdinaryReflection
import Langlands.Global.RankinSelberg.RealPairedReflectedOrdinaryTransfer

/-! # Normalized reflection from ordinary dual tests to real paired tests -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local notation:max "L[" ds "," es "]" => fun (z : ℂ) => ((realPairLFactor ds es).denominator z)⁻¹

/-- The real pair factor is nonzero on a sufficiently far right half-plane. -/
theorem realPairFactor_eventually_ne_zero (ds es : List RealBlock) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → L[ds, es] s ≠ 0 := by
  obtain ⟨b, hb⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es)
  exact ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩

namespace RealJacquet.HasRealPairNormalizedGrowth

/-- The normalized functional equation holds for any ordinary normalizations of the two
integrals in a real pair. -/
theorem ordinaryNormalization_eq
    {ds es dds ees : List RealBlock} {b : ℝˣ} {c : NNReal} {hc : 0 < c}
    {sign : ℂ} {Z Zd : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign Z Zd)
    (N : OrdinaryIntegralNormalization Z L[ds, es])
    (Nd : OrdinaryIntegralNormalization Zd L[dds, ees]) (s : ℂ) :
    Nd.value (1 - s) = sign * (realPairEpsilon ds es b c hc s : ℂ) * N.value s := by
  obtain ⟨P, Pd, hP, hPd, _, _, ⟨σ, hRight⟩, hEq⟩ := h
  have mkNorm (xs ys : List RealBlock) (U F : ℂ → ℂ) (hF : Differentiable ℂ F)
      (hU : ∀ z : ℂ, σ < z.re → F z = (realPairLFactor xs ys).denominator z * U z) :
      ∃ M : OrdinaryIntegralNormalization U L[xs, ys], M.value = F := by
    obtain ⟨b, hb⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks xs ys)
    refine ⟨⟨F, fun z _ => hF.analyticAt z, max σ b, fun z hz => ?_⟩, rfl⟩
    have hd : (realPairLFactor xs ys).denominator z ≠ 0 := hb z ((le_max_right _ _).trans_lt hz)
    rw [hU z ((le_max_left _ _).trans_lt hz), mul_comm ((realPairLFactor xs ys).denominator z),
      mul_assoc, mul_inv_cancel₀ hd, mul_one]
  obtain ⟨M, hM⟩ := mkNorm ds es Z P hP (fun z hz => (hRight z hz).1)
  obtain ⟨Md, hMd⟩ := mkNorm dds ees Zd Pd hPd (fun z hz => (hRight z hz).2)
  rw [N.value_eq_of_factor_ne_zero M (realPairFactor_eventually_ne_zero ds es),
    Nd.value_eq_of_factor_ne_zero Md (realPairFactor_eventually_ne_zero dds ees), hM, hMd]
  exact hEq s

end RealJacquet.HasRealPairNormalizedGrowth

namespace RealPairedRankRaising

open CompletedProjectiveRepresentation RealPaddedExponential
open RealPaddedWhittakerProduct (oppositeScale)
open RealPairedSmoothRowAbsorption (slot)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealLocalJacquet (dualBlock)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "N" => fun m : ℕ => Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ

variable (r t : ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, G (pairRanks r t i) →* (E i →L[ℂ] E i))

local notation "n" => pairRanks r t
local notation "A" => fun i => Matrix (Fin (n i + 1)) (Fin (n i + 1)) ℝ
local notation "B" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, B)

private local instance : ChartedSpace B Bˣ :=
  (Units.isOpenEmbedding_val (R := B)).singletonChartedSpace
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "ord" => fun hm μ T v => ordinaryPaddedPairIntegral n E R t hm μ T (v, none)
local notation "rect" => fun h a μ T v s => ∫ p, unequalPairedDualKernel r t E R h T v s p ∂(realUnequalDualMeasure (r := r) a μ)
local notation "reflectedOrdinary" => fun h (μ : RealQuotientMeasureData t) T v s =>
  ∫ q, reflectedOrdinaryKernel r t E R h T v s q ∂μ.measure

omit [∀ i, CompleteSpace (E i)] in
/-- On a pure pair the reflected ordinary kernel is the actual ordinary kernel on the two
Weyl inverse-transpose coefficient functions. -/
theorem reflectedOrdinaryKernel_pure (h : t < r) (T : D →L[ℂ] ℂ) (L : ∀ i, D₀ i →L[ℂ] ℂ)
    (hT : ∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) (v : ∀ i, D₀ i) (s : ℂ) :
    reflectedOrdinaryKernel r t E R h T (pureSmooth A R v) s = realUnequalIntegrand h
      (ArchimedeanLocal.dualFunction (r + 1) (slotCoefficient n R L v 0))
      (ArchimedeanLocal.dualFunction (t + 1) (slotCoefficient n R L v 1)) s := by
  funext q
  change reflectedPairCoefficient r t E R 1 T (pureSmooth A R v)
      (padGL (Nat.succ_le_succ h.le) q.out) q.out * _ = _
  rw [reflectedPairCoefficient_pure r t E R _ T L hT, mul_one]
  rfl

/-- The ordinary integral of the two reflected smooth coefficients, normalized by the dual
factor, gives a finite sum of primal paired normalized values after spectral reflection and
multiplication by the common epsilon factor and sign. -/
def RealPairedUnequalNormalizedReflectionStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (h : t < r) (hm : ∀ i, t ≤ n i) (a : ℝˣ) (μ : RealQuotientMeasureData t) (T : D →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    ∀ (ds es : List RealBlock) (sign : ℂ),
      let c := NNReal.sqrt ‖(a : ℝ)‖₊
      let hc : 0 < c := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
      (∀ v : D, HasRealPairNormalizedGrowth ds es (ds.map dualBlock) (es.map dualBlock) (-a) c hc sign
        (ord hm μ T v) (rect h a μ T v)) →
      ∀ v : D, ∃ (k : ℕ) (u : Fin k → D)
        (Nu : ∀ i, OrdinaryIntegralNormalization (ord hm μ T (u i)) L[ds, es]),
        ∀ (Nd : OrdinaryIntegralNormalization (reflectedOrdinary h μ T v)
          L[ds.map dualBlock, es.map dualBlock]) (s : ℂ),
          Nd.value (1 - s) = sign * (realPairEpsilon ds es (-a) c hc s : ℂ) * ∑ i, (Nu i).value s

set_option maxHeartbeats 950000 in
theorem realPairedUnequalNormalizedReflection : RealPairedUnequalNormalizedReflectionStatement r t E R := by
  intro hR h hm a μ T hCov ds es sign c hc hG v
  obtain ⟨σ, hRep⟩ := realPairedReflectedOrdinaryTransfer r t E R hR h a μ T hCov
  obtain ⟨k, u, hu⟩ := hRep v
  let Z (i : Fin k) := ord hm μ T (u i)
  let Zd (i : Fin k) := rect h a μ T (u i)
  let Nu (i : Fin k) := (hG (u i)).ordinaryNormalization.some
  let Zsum (s : ℂ) := ∑ i, Z i s
  have hSum : HasRealPairNormalizedGrowth ds es (ds.map dualBlock) (es.map dualBlock) (-a) c hc sign
      Zsum (reflectedOrdinary h μ T v) := by
    exact (HasRealPairNormalizedGrowth.sum Finset.univ Z Zd (fun i _ => hG (u i))).congr (τ := σ)
      (fun _ _ => rfl) (fun s hs => (hu s hs).2.symm)
  have hRight : ∃ bound : ℝ, ∀ s : ℂ, bound < s.re → Zsum s = (∑ i, (Nu i).value s) * L[ds, es] s := by
    choose b hb using fun i => (Nu i).eq_on_right
    obtain ⟨bound, hB⟩ := (Set.finite_range b).bddAbove
    refine ⟨bound, fun s hs => ?_⟩
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hb i s ((hB (Set.mem_range_self i)).trans_lt hs)
  let Nsum : OrdinaryIntegralNormalization Zsum L[ds, es] :=
    ⟨fun s => ∑ i, (Nu i).value s,
      fun s hs => Finset.analyticAt_fun_sum _ fun i _ => (Nu i).analytic s hs, hRight⟩
  exact ⟨k, u, Nu, fun Nd s => hSum.ordinaryNormalization_eq Nsum Nd s⟩

end RealPairedRankRaising
end Langlands.Global.RankinSelbergGlobal
