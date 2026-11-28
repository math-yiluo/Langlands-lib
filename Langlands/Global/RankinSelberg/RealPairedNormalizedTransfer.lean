import Langlands.Global.RankinSelberg.RealPairedRankTransfer
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness

/-! # Normalization under the finite real paired rank comparison -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 750000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal CompletedProjectiveRepresentation

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "Vec" => fun n : ℕ => Fin (n + 1) → ℝ

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "Terms" => fun m => D × Option (𝓢(Vec m, ℂ))

/-- The integral for a padded pair, with the determinant exponent supplied directly. -/
def paddedPairIntegral (m : ℕ) (hm : ∀ i, m ≤ n i) (μ : RealQuotientMeasureData m)
    (L : D →L[ℂ] ℂ) (t : Terms m) (s : ℂ) : ℂ :=
  ∫ q, paddedPairKernel n E R m hm L t s q ∂μ.measure

/-- The lower common-rank integral inherits a finite normalized sum with the terminal factor. -/
def RealPairedNormalizedTransferStatement : Prop :=
  ∀ (top : ℕ) (hTop : ∀ i, top ≤ n i) (μ : (m : ℕ) → RealQuotientMeasureData m)
    (L : D →L[ℂ] ℂ) (r : ℕ) (hr : r < top) (LFactor : ℂ → ℂ),
    HasPairedRankTransfer n E R top hTop μ L r hr →
    (∀ t : Terms top, IsPairedTerminalRow n top t.2 →
      ∃ _N : OrdinaryIntegralNormalization (paddedPairIntegral n E R top hTop (μ top) L t) LFactor,
        ∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Integrable (paddedPairKernel n E R top hTop L t s) (μ top).measure) →
    ∃ c : ℝ, 0 < c ∧ ∀ v : D,
      ∃ (k : ℕ) (t : Fin k → Terms top), (∀ i, IsPairedTerminalRow n top (t i).2) ∧
        ∃ (Nt : ∀ i, OrdinaryIntegralNormalization (paddedPairIntegral n E R top hTop (μ top) L (t i)) LFactor)
          (N : OrdinaryIntegralNormalization
            (fun s => paddedPairIntegral n E R r (fun i => hr.le.trans (hTop i)) (μ r) L (v, none)
              (s - (top - r : ℕ))) LFactor),
          ∀ s : ℂ, (c : ℂ) * N.value s = ∑ i, (Nt i).value s

theorem realPairedNormalizedTransfer : RealPairedNormalizedTransferStatement n E R := by
  intro top hTop μ L r hr LFactor hTransfer hEntire
  obtain ⟨c, hc, hRank⟩ := hTransfer
  refine ⟨c, hc, fun v => ?_⟩
  obtain ⟨k, t, ht, hV⟩ := hRank v
  choose Nt b hb using fun i => hEntire (t i) (ht i)
  choose d hd using fun i => (Nt i).eq_on_right
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let F (s : ℂ) := (c : ℂ)⁻¹ * ∑ i, (Nt i).value s
  refine ⟨k, t, ht, Nt, ⟨F, ?_, ?_⟩, fun s => ?_⟩
  · intro s hs
    apply analyticAt_const.fun_mul
    exact Finset.analyticAt_fun_sum _ fun i _ => (Nt i).analytic s hs
  · obtain ⟨M, hM⟩ := (Set.finite_range (fun i => max (b i) (d i))).bddAbove
    refine ⟨M, fun s hs => ?_⟩
    have hAbove (i : Fin k) : max (b i) (d i) < s.re :=
      (hM (Set.mem_range_self i)).trans_lt hs
    have hi (i : Fin k) := hb i s ((le_max_left _ _).trans_lt (hAbove i))
    have he (i : Fin k) := hd i s ((le_max_right _ _).trans_lt (hAbove i))
    have hEq := (hV s hi).2
    change (c : ℂ) * paddedPairIntegral n E R r (fun i => hr.le.trans (hTop i)) (μ r) L (v, none)
      (s - (top - r : ℕ)) = ∑ i, paddedPairIntegral n E R top hTop (μ top) L (t i) s at hEq
    simp_rw [he, ← Finset.sum_mul] at hEq
    apply mul_left_cancel₀ hc'
    rw [hEq]
    dsimp [F]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]
  · dsimp [F]
    rw [← mul_assoc, mul_inv_cancel₀ hc', one_mul]

/-- A normalized lower integral belongs to any subspace containing the normalized terminal tests
when the common factor is nonzero on a right half-plane. -/
theorem normalized_lower_mem (top : ℕ) (hTop : ∀ i, top ≤ n i)
    (μ : (m : ℕ) → RealQuotientMeasureData m) (L : D →L[ℂ] ℂ)
    (r : ℕ) (hr : r < top) (LFactor : ℂ → ℂ) (hTransfer : HasPairedRankTransfer n E R top hTop μ L r hr)
    (hEntire : ∀ t : Terms top, IsPairedTerminalRow n top t.2 →
      ∃ _N : OrdinaryIntegralNormalization (paddedPairIntegral n E R top hTop (μ top) L t) LFactor,
        ∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Integrable (paddedPairKernel n E R top hTop L t s) (μ top).measure)
    (hFactor : ∃ b : ℝ, ∀ s : ℂ, b < s.re → LFactor s ≠ 0)
    (V : Submodule ℂ (ℂ → ℂ))
    (hV : ∀ t : Terms top, IsPairedTerminalRow n top t.2 →
      ∀ N : OrdinaryIntegralNormalization (paddedPairIntegral n E R top hTop (μ top) L t) LFactor,
        N.value ∈ V)
    (v : D) (N : OrdinaryIntegralNormalization
      (fun s => paddedPairIntegral n E R r (fun i => hr.le.trans (hTop i)) (μ r) L (v, none)
        (s - (top - r : ℕ))) LFactor) :
    N.value ∈ V := by
  obtain ⟨c, hc, h⟩ := realPairedNormalizedTransfer n E R top hTop μ L r hr LFactor hTransfer hEntire
  obtain ⟨k, t, ht, Nt, N', he⟩ := h v
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hf : N'.value = (c : ℂ)⁻¹ • ∑ i, (Nt i).value := by
    funext s
    change N'.value s = (c : ℂ)⁻¹ * (∑ i, (Nt i).value) s
    rw [Finset.sum_apply, ← he s, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [N.value_eq_of_factor_ne_zero N' hFactor, hf]
  exact V.smul_mem _ (V.sum_mem fun i _ => hV (t i) (ht i) (Nt i))

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
