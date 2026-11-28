import Langlands.Global.RankinSelberg.RealCompactParabolicRowFactorization
import Langlands.Global.RankinSelberg.RealPairedParabolicKernel

/-! # Primal comparison at a strict lower parabolic cut -/

noncomputable section

open MeasureTheory TopologicalSpace
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1100000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation
open RealParabolicCompactSection RealParabolicPrimalIntegral

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Q" => fun n : ℕ => Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ
local notation "N" => fun n : ℕ => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "Row" => fun n : ℕ => Fin (n + 1) → ℝ
local notation "X" => fun t p : ℕ => Matrix (Fin (t + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun t p => 𝓓((⊤ : Opens (X t p)), ℂ)
local notation "last" => Langlands.RankinSelberg.lastRow

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => fun i => DerivativeSmoothVectors.representation 𝓘(ℝ, A i) (R i)
local notation "Terms" => fun m => D × Option (𝓢(Row m, ℂ))

/-- The terminal determinant exponent is shifted by the half-sum of the two rank gaps. -/
def ordinaryPaddedPairKernel (m : ℕ) (hm : ∀ i, m ≤ n i) (T : D →L[ℂ] ℂ)
    (v : Terms m) (s : ℂ) (q : Q m) : ℂ :=
  paddedPairKernel n E R m hm T v (s - pairedDetShift n m) q

/-- The integral of the padded pair with the ordinary spectral parameter. -/
def ordinaryPaddedPairIntegral (m : ℕ) (hm : ∀ i, m ≤ n i) (μ : RealQuotientMeasureData m)
    (T : D →L[ℂ] ℂ) (v : Terms m) (s : ℂ) : ℂ :=
  ∫ q, ordinaryPaddedPairKernel n E R m hm T v s q ∂μ.measure

/-- Terminal tests have entire normalized values and absolutely convergent initial integrals. -/
def HasPairedTerminalNormalizations (m : ℕ) (hm : ∀ i, m ≤ n i) (μ : RealQuotientMeasureData m)
    (T : D →L[ℂ] ℂ) (LFactor : ℂ → ℂ) : Prop :=
  ∀ v : Terms m, IsPairedTerminalRow n m v.2 →
    (Nonempty (OrdinaryIntegralNormalization (ordinaryPaddedPairIntegral n E R m hm μ T v) LFactor)) ∧
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (ordinaryPaddedPairKernel n E R m hm T v s) μ.measure

variable [∀ i, CompleteSpace (E i)]

private theorem eq_other_slot {i j k : Fin 2} (hij : i ≠ j) (hki : k ≠ i) : k = j := by
  have h : ∀ i j k : Fin 2, i ≠ j → k ≠ i → k = j := by decide
  exact h i j k hij hki

private def purePairAt {F : Fin 2 → Type*} {i j : Fin 2} (hij : i ≠ j) (v : F i) (w : F j) (k : Fin 2) : F k :=
  if h : k = i then h.symm ▸ v else (eq_other_slot hij h).symm ▸ w

@[simp] private theorem purePairAt_left {F : Fin 2 → Type*} {i j : Fin 2} (hij : i ≠ j) (v : F i) (w : F j) :
    purePairAt hij v w i = v := by simp [purePairAt]

@[simp] private theorem purePairAt_right {F : Fin 2 → Type*} {i j : Fin 2} (hij : i ≠ j) (v : F i) (w : F j) :
    purePairAt hij v w j = w := by simp [purePairAt, hij.symm]

/-- When the leading cut lies below both ranks, the ordinary lower integral normalized by the
terminal factor belongs to any subspace containing the normalized terminal tests. -/
def RealPairedStrictPrimalAtStatement : Prop :=
  ∀ (i j : Fin 2) (_ : i ≠ j) (a : ℝˣ) (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
    (∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) →
    IsContinuousRepresentation (R j) →
    (∀ (u : N (n j)) (v : D₀ j), L j (act j u.val v) = realWhittakerCharacter (-a) u.val * L j v) →
    ∀ (t m p : ℕ) (ht : t < m) (hm : ∀ i, m ≤ n i) (μ : (j : ℕ) → RealQuotientMeasureData j)
      (U : G t → ℂ),
      (∀ φ : Test t p, ∃ v : D₀ i, HasLeadingBlockRestriction (ht.trans_le (hm i))
        (fun g => L i (act i g v)) U (compactRowProfile a φ)) →
      HasPairedRankTransfer n E R m hm μ T t ht →
      ∀ LFactor : ℂ → ℂ, HasPairedTerminalNormalizations n E R m hm (μ m) T LFactor →
      ∀ S : Submodule ℂ (ℂ → ℂ),
        (∀ v : Terms m, IsPairedTerminalRow n m v.2 →
          ∀ M : OrdinaryIntegralNormalization (ordinaryPaddedPairIntegral n E R m hm (μ m) T v) LFactor,
            M.value ∈ S) →
        ∀ w : D₀ j, ∃ M : OrdinaryIntegralNormalization
          (realUnequalIntegral (ht.trans_le (hm j)) (μ t) (fun g => L j (act j g w)) U) LFactor,
          M.value ∈ S

theorem realPairedStrictPrimalAt : RealPairedStrictPrimalAtStatement n E R := by
  intro i₀ j₀ hij a L T hT hR hL t m p ht hm μ U hLift hTransfer LFactor hEntire S hS w
  let δ := pairedDetShift n m
  let hsmall (i : Fin 2) := ht.le.trans (hm i)
  let hrev : t < n j₀ := ht.trans_le (hm j₀)
  let V (z : D₀ j₀) (g : G (n j₀)) := L j₀ (act j₀ g z)
  obtain ⟨k, w', φ, hColumn⟩ := realCompactParabolicRowFactorization (n j₀) t p hrev (E j₀) (R j₀) hR a (L j₀) hL w
  choose w₀ hLeading using fun i => hLift (φ i)
  let v (i : Fin k) : ∀ j, D₀ j := purePairAt hij (w₀ i) (w' i)
  let K (i : Fin k) (s : ℂ) := paddedPairKernel n E R t hsmall T (pureSmooth A R (v i), none)
      (s - δ - (m - t : ℕ))
  have hK (i : Fin k) (s : ℂ) : K i s = fun q =>
      realUnequalIntegrand hrev (V (w' i)) U s q * compactRowProfile a (φ i) (last q.out) := by
    have hi : v i i₀ = w₀ i := purePairAt_left hij _ _
    have hj : v i j₀ = w' i := purePairAt_right hij _ _
    have hW : HasLeadingBlockRestriction (ht.trans_le (hm i₀))
        (slotCoefficient n R L (v i) i₀) U (compactRowProfile a (φ i)) := by
      change HasLeadingBlockRestriction (ht.trans_le (hm i₀))
        (fun g => L i₀ (act i₀ g (v i i₀))) U (compactRowProfile a (φ i))
      rw [hi]
      exact hLeading i
    have hV : slotCoefficient n R L (v i) j₀ = V (w' i) := by
      funext g
      change L j₀ (act j₀ g (v i j₀)) = L j₀ (act j₀ g (w' i))
      rw [hj]
    unfold K
    rw [pairedParabolicKernel_of_leading n R i₀ j₀ hij L T hT t m ht hm (v i) U _ hW s, hV]

  have hLower (s : ℂ) : realUnequalIntegrand hrev (V w) U s = fun q => ∑ i, K i s q := by
    funext q
    simp_rw [hK]
    let g := q.out
    let P := ArchimedeanLocal.detPower realNormalizedAbs g (s - ((n j₀ - t : ℕ) : ℂ) / 2)
    change V w (padGL (Nat.succ_le_succ hrev.le) g) * U g * P = ∑ i,
      (V (w' i) (padGL (Nat.succ_le_succ hrev.le) g) * U g * P) * compactRowProfile a (φ i) (last g)
    rw [show V w (padGL (Nat.succ_le_succ hrev.le) g) = ∑ i,
      V (w' i) (padGL (Nat.succ_le_succ hrev.le) g) * compactRowProfile a (φ i) (last g) from hColumn g]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨c, hc, hRaise⟩ := hTransfer
  choose l terms hRow hCompare using fun i => hRaise (pureSmooth A R (v i))
  let J := Σ i : Fin k, Fin (l i)
  have hData (j : J) := hEntire (terms j.1 j.2) (hRow j.1 j.2)
  let N' (j : J) := (hData j).1.some
  choose b hb using fun j => (hData j).2
  choose d hd using fun j => (N' j).eq_on_right
  obtain ⟨B, hB⟩ := (Set.finite_range (fun j : J => max (b j) (d j))).bddAbove
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let M : ℂ → ℂ := (c : ℂ)⁻¹ • ∑ j : J, (N' j).value
  have hM (s : ℂ) : M s = (c : ℂ)⁻¹ * ∑ j : J, (N' j).value s := by
    simp only [M, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  refine ⟨⟨M, ?_, ⟨B, ?_⟩⟩, S.smul_mem _ (S.sum_mem fun j _ => hS _ (hRow j.1 j.2) (N' j))⟩
  · intro s hs
    rw [funext hM]
    exact analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun j _ => (N' j).analytic s hs)
  · intro s hs
    have hAbove (j : J) : max (b j) (d j) < s.re := (hB (Set.mem_range_self j)).trans_lt hs
    have hInt (j : J) := hb j s ((le_max_left _ _).trans_lt (hAbove j))
    have hN (j : J) := hd j s ((le_max_right _ _).trans_lt (hAbove j))
    have hCmp (i : Fin k) := hCompare i (s - δ) (fun j => hInt ⟨i, j⟩)
    have hRaw : (c : ℂ) * realUnequalIntegral hrev (μ t) (V w) U s =
        ∑ j : J, ordinaryPaddedPairIntegral n E R m hm (μ m) T (terms j.1 j.2) s := by
      calc
        _ = (c : ℂ) * ∑ i, ∫ q, K i s q ∂(μ t).measure := by
          change (c : ℂ) * (∫ q, realUnequalIntegrand hrev (V w) U s q ∂(μ t).measure) = _
          rw [hLower, integral_finsetSum _ fun i _ => (hCmp i).1]
        _ = ∑ i, ∑ j, ordinaryPaddedPairIntegral n E R m hm (μ m) T (terms i j) s := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (hCmp i).2
        _ = _ := (Fintype.sum_sigma (fun j : J =>
          ordinaryPaddedPairIntegral n E R m hm (μ m) T (terms j.1 j.2) s)).symm
    apply mul_left_cancel₀ hc'
    rw [hRaw, hM, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc', one_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hN j

/-- The strict lower comparison for the cut in the first slot. -/
def RealPairedStrictPrimalStatement : Prop :=
  ∀ (a : ℝˣ) (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
    (∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i)) →
    IsContinuousRepresentation (R 1) →
    (∀ (u : N (n 1)) (v : D₀ 1), L 1 (act 1 u.val v) = realWhittakerCharacter (-a) u.val * L 1 v) →
    ∀ (t m p : ℕ) (ht : t < m) (hm : ∀ i, m ≤ n i) (μ : (j : ℕ) → RealQuotientMeasureData j)
      (U : G t → ℂ),
      (∀ φ : Test t p, ∃ v : D₀ 0, HasLeadingBlockRestriction (ht.trans_le (hm 0))
        (fun g => L 0 (act 0 g v)) U (compactRowProfile a φ)) →
      HasPairedRankTransfer n E R m hm μ T t ht →
      ∀ LFactor : ℂ → ℂ, HasPairedTerminalNormalizations n E R m hm (μ m) T LFactor →
      ∀ S : Submodule ℂ (ℂ → ℂ),
        (∀ v : Terms m, IsPairedTerminalRow n m v.2 →
          ∀ M : OrdinaryIntegralNormalization (ordinaryPaddedPairIntegral n E R m hm (μ m) T v) LFactor,
            M.value ∈ S) →
        ∀ w : D₀ 1, ∃ M : OrdinaryIntegralNormalization
          (realUnequalIntegral (ht.trans_le (hm 1)) (μ t) (fun g => L 1 (act 1 g w)) U) LFactor,
          M.value ∈ S

theorem realPairedStrictPrimal : RealPairedStrictPrimalStatement n E R := by
  exact realPairedStrictPrimalAt n E R 0 1 (by decide)

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, Langlands.GeneralLinear ((n i) + 1) ℝ →* (E i →L[ℂ] E i))

/-- The assertion for representations on complex Banach spaces. -/
def RealPairedStrictPrimalAtBanachStatement [∀ i, CompleteSpace (E i)] : Prop :=
  RealPairedStrictPrimalAtStatement n E R

theorem realPairedStrictPrimalAtBanach [∀ i, CompleteSpace (E i)] : RealPairedStrictPrimalAtBanachStatement n E R :=
  realPairedStrictPrimalAt n E R

/-- The assertion for representations on complex Banach spaces. -/
def RealPairedStrictPrimalBanachStatement [∀ i, CompleteSpace (E i)] : Prop :=
  RealPairedStrictPrimalStatement n E R

theorem realPairedStrictPrimalBanach [∀ i, CompleteSpace (E i)] : RealPairedStrictPrimalBanachStatement n E R :=
  realPairedStrictPrimal n E R

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
