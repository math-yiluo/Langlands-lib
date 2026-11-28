import Langlands.Global.RankinSelberg.RealCompactParabolicLeading

/-! # Primal normalized transfer from compact real parabolic sections -/

noncomputable section

open MeasureTheory TopologicalSpace
open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Distributions SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open ArchimedeanLocal RealParabolicPrimalIntegral
open RealExactWhittakerUniqueness RealStandardCompactBanach

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "S" => fun r ds => realStandardModule (r + 1) ds
local notation "Row" => fun r => Fin (r + 1) → ℝ
local notation:max "R" r:max ds:max => representation (n := r + 1) ds
local notation:max "D" r:max ds:max => DerivativeSmoothVectors (matrixModel ℝ (r + 1)) (R r ds)
local notation:max "act" r:max ds:max => DerivativeSmoothVectors.representation (matrixModel ℝ (r + 1)) (R r ds)
local notation "X" => fun m p => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun m p => 𝓓((⊤ : Opens (X m p)), ℂ)
private abbrev NormPair (ds es : List RealBlock) (J : ℂ → ℂ) :=
  OrdinaryIntegralNormalization J (fun s => ((realPairLFactor ds es).denominator s)⁻¹)

/-- The right-translate coefficient of a smooth evaluation and a standard vector. -/
def smoothStandardCoefficient {r : ℕ} (ds : List RealBlock) (L : D r ds →L[ℂ] ℂ)
    (f : S r ds) (A : G r) : ℂ := L (act r ds A (derivativeEquiv ds f))

/-- The genuine Whittaker coefficient of a compact pure parabolic section. -/
def compactLiftCoefficient {m p : ℕ} {d₁ d₂ : List RealBlock}
    (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1) (L : D (p + 1 + m) (d₂ ++ d₁) →L[ℂ] ℂ)
    (f : S m d₁) (g : S p d₂) (φ : Test m p) (A : G (p + 1 + m)) : ℂ :=
  L (act (p + 1 + m) (d₂ ++ d₁) A (smoothSectionVector hm hp f g φ))

private def prependNormalization (d₁ d₂ e : List RealBlock) (I J : ℂ → ℂ) (h : I = J)
    (N : NormPair d₁ e I) : NormPair (d₂ ++ d₁) e J := by
  let M := appendLeftNormalization d₁ d₂ e I J h N
  refine ⟨M.value, M.analytic, ?_⟩
  have hFactor (s : ℂ) : (realPairLFactor (d₂ ++ d₁) e).denominator s =
      (realPairLFactor (d₁ ++ d₂) e).denominator s := by
    simp [realPairLFactor, realPairBlocks, List.flatMap_append, realLFactor_append, ReciprocalEntire.mul, mul_comm]
  simpa only [hFactor] using M.eq_on_right

/-- Compact leading lifts transfer primal normalizations at equal cut rank for their
row profiles, and at every strictly smaller comparison rank for a fixed compact profile.
The multiplier is the complementary denominator in the upper-Borel block order. -/
def RealCompactParabolicPrimalStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
    (a : ℝˣ) (L : D (p + 1 + m) (d₂ ++ d₁) →L[ℂ] ℂ)
    (L₁ : D m d₁ →L[ℂ] ℂ) (L₂ : D p d₂ →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L →
    IsSmoothWhittakerEvaluation d₁ a L₁ → IsSmoothWhittakerEvaluation d₂ a L₂ →
    L ≠ 0 → L₁ ≠ 0 → L₂ ≠ 0 →
    let h : m < p + 1 + m := by omega
    ∃ (g : S p d₂) (τ : Test m p), compactRowProfile a τ (Pi.single (Fin.last m) 1) = 1 ∧
      (∀ (f : S m d₁) (φ : Test m p) (e : List RealBlock) (V : G m → ℂ) (Q : RealQuotientMeasureData m)
        (N : NormPair d₁ e (realEqualIntegral Q (smoothStandardCoefficient d₁ L₁ f) V (compactRowProfile a φ))),
        ∃ M : NormPair (d₂ ++ d₁) e (realUnequalIntegral h Q (compactLiftCoefficient hm hp L f g φ) V),
          ∀ s, M.value s = (realPairLFactor d₂ e).denominator s * N.value s) ∧
      (∀ (t : ℕ) (ht : t < m) (f : S m d₁) (e : List RealBlock) (V : G t → ℂ) (Q : RealQuotientMeasureData t)
        (N : NormPair d₁ e (realUnequalIntegral ht Q (smoothStandardCoefficient d₁ L₁ f) V)),
        ∃ M : NormPair (d₂ ++ d₁) e (realUnequalIntegral (ht.trans h) Q (compactLiftCoefficient hm hp L f g τ) V),
          ∀ s, M.value s = (realPairLFactor d₂ e).denominator s * N.value s)

set_option maxHeartbeats 720000 in
theorem realCompactParabolicPrimal : RealCompactParabolicPrimalStatement := by
  intro m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hLne hL₁ne hL₂ne h
  obtain ⟨g, hg⟩ := realCompactParabolicLeadingRestriction m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hLne hL₁ne hL₂ne
  obtain ⟨τ, hτ⟩ := exists_compactRowProfile_basis_eq_one (m := m) (p := p) a
  refine ⟨g, τ, hτ, ?_, ?_⟩
  · intro f φ e V Q N
    let U := smoothStandardCoefficient d₁ L₁ f
    let W := compactLiftCoefficient hm hp L f g φ
    let Φ := compactRowProfile a φ
    have hW : HasLeadingBlockRestriction h W U Φ := hg f φ
    have hI : realEqualIntegral Q U V Φ = realUnequalIntegral h Q W V := by
      funext s
      change (∫ q, realEqualIntegrand U V Φ s q ∂Q.measure) = ∫ q, realUnequalIntegrand h W V s q ∂Q.measure
      rw [(realParabolicPrimalIntegral.1 _ _ h W U V Φ hW s)]
    exact ⟨prependNormalization d₁ d₂ e _ _ hI N, fun _ => rfl⟩
  · intro t ht f e V Q N
    let U := smoothStandardCoefficient d₁ L₁ f
    let W := compactLiftCoefficient hm hp L f g τ
    let Φ := compactRowProfile a τ
    have hW : HasLeadingBlockRestriction h W U Φ := hg f τ
    have hI : realUnequalIntegral ht Q U V = realUnequalIntegral (ht.trans h) Q W V := by
      funext s
      change (∫ q, realUnequalIntegrand ht U V s q ∂Q.measure) = ∫ q, realUnequalIntegrand (ht.trans h) W V s q ∂Q.measure
      rw [realParabolicPrimalIntegral.2.1 _ _ _ h ht W U V Φ hW hτ s]
    exact ⟨prependNormalization d₁ d₂ e _ _ hI N, fun _ => rfl⟩

/-- A nonzero continuous equal-rank normalized evaluation at a fixed spectral point
is detected on a compact row profile. -/
theorem exists_compactProfile_eval_ne_zero {m p : ℕ} (a : ℝˣ) (Λ : 𝓢(Row m, ℂ) →L[ℂ] ℂ) (hΛ : Λ ≠ 0) :
    ∃ φ : Test m p, Λ (compactRowProfile a φ) ≠ 0 := by
  by_contra! hzero
  apply hΛ
  have h := (denseRange_compactRowProfile (m := m) (p := p) a).equalizer Λ.continuous continuous_const
    (funext hzero)
  exact ContinuousLinearMap.ext (congrFun h)

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
