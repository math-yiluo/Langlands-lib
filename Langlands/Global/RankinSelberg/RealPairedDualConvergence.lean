import Langlands.Global.RankinSelberg.RealPairedOrdinaryKernels
import Langlands.Global.RankinSelberg.RealPairedWhittakerGauge
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence

/-! # Convergence of the reflected ordinary integrals for genuine smooth real pairs -/

noncomputable section

open Matrix MeasureTheory
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1100000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation
open RealPairedSmoothRowAbsorption (slot unitProjection_slot_self unitProjection_slot_of_ne)
open RealPairedWhittakerGauge (coefficient contMDiff_slot realPairedWhittakerGauge slot_commute)
open RealPaddedWhittakerProduct (oppositeScale)
open RealIwasawa (alpha torus npart_mul_torus_mul_kpart npart kpart alpha_torus_mul_unitary)
open RealConvergenceAnalysis (rootPos)
open RealEqualConvergence (logDet realWhittakerCharacter_mul_neg HasOrdinaryToralBound
  exists_convergence_of_toral_bound exists_norm_le_exp exp_le_mul_norm_lastRow)
open RealEqualDualConvergence (dual_torus_mul revNeg weylUnitary rootPos_revNeg sum_abs_revNeg
  fourier_rapidDecay)
open RealUnequalDualConvergence (HasRectangularToralBound realRectangularToralConvergence
  rectangular_toralExponent_le hasRectangularToralBound_of_log_bound continuous_rectangularPoint)
open RealUnequalPairConvergence (rectangularPoint_mul rectangularPoint_zero unfoldingWeyl_mem_unitary
  realWhittakerCharacter_reflected norm_realWhittakerCharacter)
open RealUnequalConvergence (padGL_mem_upperUnipotent realWhittakerCharacter_padGL)
open RealRectangularIwasawa (frob)
open Langlands.Whittaker (reflectedUnipotent weylInverseTranspose_left_unipotent)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun r : ℕ => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => fun r : ℕ => Langlands.RankinSelberg.LeftUnipotentQuotient r ℝ
local notation "N" => fun r : ℕ => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "K" => fun r : ℕ => unitaryCompact ℝ (r + 1)
local notation "Mat" => fun r : ℕ => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Row" => fun r : ℕ => Fin (r + 1) → ℝ
local notation "wt" => fun r : ℕ => Langlands.GeneralLinear.weylInverseTranspose (r + 1) ℝ
local notation "Rect" => fun r t : ℕ => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ
local notation "rect" => ArchimedeanLocal.rectangularPoint
local notation "tailWeyl" => ArchimedeanLocal.unfoldingWeyl

private theorem reflectedHeight_torus_mul_pow_le {m : ℕ} (y : Row m) (k : K m) (d : ℕ) :
    realMatrixHeight (wt m (torus y * k.val)) ^ d ≤
      (2 * ((m : ℝ) + 1) ^ 2) ^ d * Real.exp (((2 * d : ℕ) : ℝ) * ∑ j, |y j|) := by
  let F (g : G m) : ℂ := (realMatrixHeight g ^ d : ℝ)
  have h : realMatrixHeight (wt m (torus y * k.val)) ^ d =
      realMatrixHeight (torus (revNeg y) * (weylUnitary k).val) ^ d := by
    apply Complex.ofReal_injective
    change ArchimedeanLocal.dualFunction (m + 1) F (torus y * k.val) = F _
    exact dual_torus_mul F y k
  rw [h, ← sum_abs_revNeg y]
  exact RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le (revNeg y) (weylUnitary k) d

variable (r t : ℕ) (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (pairRanks r t i) →* (E i →L[ℂ] E i))

local notation "n" => pairRanks r t
local notation "A" => fun i => Mat (n i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)
local notation "act" => DerivativeSmoothVectors.representation I P

/-- Apply the two Weyl inverse transposes, with a right multiplier in the first slot. -/
def reflectedPairCoefficient (w : G r) (T : D →L[ℂ] ℂ) (v : D) (g : G r) (h : G t) : ℂ :=
  coefficient n E R T 0 1 (wt t h) v (wt r (g * w))

/-- The coefficient of the reflected rectangular integral before determinant weighting. -/
def unequalDualPairCoefficient (h : t < r) (T : D →L[ℂ] ℂ) (v : D) (p : G t × Rect r t) : ℂ :=
  reflectedPairCoefficient r t E R (tailWeyl h) T v (rect h p.1 p.2) p.1

/-- The ordinary reflected rectangular kernel on the product quotient and rectangle space. -/
def unequalPairedDualKernel (h : t < r) (T : D →L[ℂ] ℂ) (v : D) (s : ℂ) (p : Q t × Rect r t) : ℂ :=
  unequalDualPairCoefficient r t E R h T v (p.1.out, p.2) *
    ArchimedeanLocal.detPower realNormalizedAbs p.1.out (s - ((r - t : ℕ) : ℂ) / 2)

/-- On pure smooth tensors the reflected coefficient is the product of the two scalar
Weyl inverse-transpose coefficients. -/
theorem reflectedPairCoefficient_pure (w : G r) (T : D →L[ℂ] ℂ) (L : ∀ i, D₀ i →L[ℂ] ℂ)
    (hT : ∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i))
    (v : ∀ i, D₀ i) (g : G r) (h : G t) :
    reflectedPairCoefficient r t E R w T (pureSmooth A R v) g h =
      L 0 (DerivativeSmoothVectors.representation 𝓘(ℝ, A 0) (R 0) (wt r (g * w)) (v 0)) *
        L 1 (DerivativeSmoothVectors.representation 𝓘(ℝ, A 1) (R 1) (wt t h) (v 1)) := by
  unfold reflectedPairCoefficient coefficient
  rw [representation_pureSmooth, hT, Fin.prod_univ_two]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [map_mul, unitProjection_slot_self, unitProjection_slot_of_ne n h01,
    unitProjection_slot_of_ne n h01.symm, one_mul, mul_one]

/-- The pure reflected rectangular kernel equals the ordinary scalar dual kernel. -/
theorem unequalPairedDualKernel_pure (h : t < r) (T : D →L[ℂ] ℂ) (L : ∀ i, D₀ i →L[ℂ] ℂ)
    (hT : ∀ v : ∀ i, D₀ i, T (pureSmooth A R v) = ∏ i, L i (v i))
    (v : ∀ i, D₀ i) (s : ℂ) :
    unequalPairedDualKernel r t E R h T (pureSmooth A R v) s =
      realUnequalDualKernel h
        (fun g => L 0 (DerivativeSmoothVectors.representation 𝓘(ℝ, A 0) (R 0) g (v 0)))
        (fun g => L 1 (DerivativeSmoothVectors.representation 𝓘(ℝ, A 1) (R 1) g (v 1))) s := by
  funext p
  unfold unequalPairedDualKernel unequalDualPairCoefficient
  rw [reflectedPairCoefficient_pure r t E R _ T L hT]
  rfl

private theorem continuous_reflectedPairCoefficient (w : G r) (T : D →L[ℂ] ℂ) (v : D) :
    Continuous (fun p : G r × G t => reflectedPairCoefficient r t E R w T v p.1 p.2) := by
  refine (contMDiff_smoothScalarCoefficient P T v).continuous.comp ?_
  exact ((contMDiff_slot n 1).continuous.comp ((wt t).continuous.comp continuous_snd)).mul
    ((contMDiff_slot n 0).continuous.comp ((wt r).continuous.comp (continuous_fst.mul continuous_const)))

/-- The two reflected coefficients have the reversed left Whittaker characters. -/
theorem reflectedPairCoefficient_mul (w : G r) (T : D →L[ℂ] ℂ) (a : ℝˣ)
    (hCov : ∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) (v : D) :
    (∀ (u : N r) (g : G r) (h : G t), reflectedPairCoefficient r t E R w T v (u.val * g) h =
      realWhittakerCharacter (-a) u.val * reflectedPairCoefficient r t E R w T v g h) ∧
    ∀ (u : N t) (g : G r) (h : G t), reflectedPairCoefficient r t E R w T v g (u.val * h) =
      realWhittakerCharacter a u.val * reflectedPairCoefficient r t E R w T v g h := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 := h01.symm
  refine ⟨fun u g h => ?_, fun u g h => ?_⟩
  · unfold reflectedPairCoefficient coefficient
    rw [mul_assoc, weylInverseTranspose_left_unipotent]
    let u' := reflectedUnipotent u
    have he : slot n 1 (wt t h) * slot n 0 (u'.val * wt r (g * w)) =
        slot n 0 u'.val * (slot n 1 (wt t h) * slot n 0 (wt r (g * w))) := by
      rw [(slot n 0).map_mul, ← mul_assoc, ← (slot_commute n h01 u'.val (wt t h)).eq, mul_assoc]
    rw [he, map_mul, Module.End.mul_apply, hCov 0 u']
    simp only [oppositeScale, ite_true]
    rw [realWhittakerCharacter_reflected]
  · unfold reflectedPairCoefficient coefficient
    rw [weylInverseTranspose_left_unipotent, (slot n 1).map_mul, mul_assoc, map_mul,
      Module.End.mul_apply, hCov 1 (reflectedUnipotent u)]
    simp only [oppositeScale, ite_eq_right h10, realWhittakerCharacter_reflected, neg_neg]

private theorem unequalDualPairCoefficient_invariant (h : t < r) (a : ℝˣ) (T : D →L[ℂ] ℂ)
    (hCov : ∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v)
    (v : D) (u : N t) (g : G t) (x : Rect r t) :
    unequalDualPairCoefficient r t E R h T v (u.val * g, x) = unequalDualPairCoefficient r t E R h T v (g, x) := by
  have hV := reflectedPairCoefficient_mul r t E R (tailWeyl h) T a hCov v
  change reflectedPairCoefficient r t E R (tailWeyl h) T v (rect h (u.val * g) x) (u.val * g) =
    reflectedPairCoefficient r t E R (tailWeyl h) T v (rect h g x) g
  rw [rectangularPoint_mul, rectangularPoint_zero]
  let u' : N r := ⟨padGL (Nat.succ_le_succ h.le) u.val, padGL_mem_upperUnipotent _ u.2⟩
  change reflectedPairCoefficient r t E R (tailWeyl h) T v (u'.val * rect h g x) (u.val * g) = _
  rw [hV.1 u', hV.2 u]
  have huChar : realWhittakerCharacter (-a) u'.val = realWhittakerCharacter (-a) u.val :=
    realWhittakerCharacter_padGL h _ _ _
  rw [huChar]
  have he : realWhittakerCharacter (-a) u.val * realWhittakerCharacter a u.val = 1 :=
    by simpa only [neg_neg] using realWhittakerCharacter_mul_neg (-a) u.val
  rw [← mul_assoc, he, one_mul]

variable [∀ i, CompleteSpace (E i)]

/-- The reflected pair has the axial toral gauge at any Iwasawa point when the right
multiplier is orthogonal. -/
theorem reflectedPairCoefficient_gauge (hR : ∀ i, IsContinuousRepresentation (R i))
    (w : G r) (hw : w ∈ K r) (a : ℝˣ) (T : D →L[ℂ] ℂ)
    (hCov : ∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) :
    ∃ d : ℕ, ∀ (v : D) (M : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : G r) (h' : G t), ‖reflectedPairCoefficient r t E R w T v g h'‖ ≤
        C * Real.exp (-(M : ℝ) * rootPos (alpha g) + ((2 * d : ℕ) : ℝ) * ∑ j, |alpha g j|) *
          realMatrixHeight (wt t h') ^ d := by
  obtain ⟨d, hG⟩ := realPairedWhittakerGauge n E R hR a T hCov
  refine ⟨d, fun v M => ?_⟩
  let V := reflectedPairCoefficient r t E R w T v
  have hV := reflectedPairCoefficient_mul r t E R w T a hCov v
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨C, hC, hCbd⟩ := hG 0 1 h01 v M
  refine ⟨C, hC, fun g h' => ?_⟩
  change ‖V g h'‖ ≤ _
  have hg : g = (npart g).val * (torus (alpha g) * (kpart g).val) := by
    rw [← mul_assoc, npart_mul_torus_mul_kpart]
  have hc : ‖V g h'‖ = ‖V (torus (alpha g) * (kpart g).val) h'‖ := by
    conv_lhs => rw [hg]
    change ‖reflectedPairCoefficient r t E R w T v
      ((npart g).val * (torus (alpha g) * (kpart g).val)) h'‖ = _
    rw [hV.1 (npart g), norm_mul, norm_realWhittakerCharacter, one_mul]
  let k : K r := ⟨(kpart g).val * w, (unitaryCompact ℝ (r + 1)).mul_mem (kpart g).2 hw⟩
  have he : V (torus (alpha g) * (kpart g).val) h' =
      coefficient n E R T 0 1 (wt t h') v (torus (revNeg (alpha g)) * (weylUnitary k).val) := by
    unfold V reflectedPairCoefficient
    rw [mul_assoc]
    change ArchimedeanLocal.dualFunction (r + 1) (coefficient n E R T 0 1 (wt t h') v)
      (torus (alpha g) * k.val) = _
    exact dual_torus_mul _ _ k
  rw [hc, he]
  have hb := hCbd (revNeg (alpha g)) (weylUnitary k) (wt t h')
  rw [rootPos_revNeg, sum_abs_revNeg] at hb
  exact hb

omit [∀ i, CompleteSpace (E i)] in
private theorem unequalDualPairCoefficient_toralBound (h : t < r) (T : D →L[ℂ] ℂ) (v : D) (d : ℕ)
    (hToral : ∀ (M : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : G r) (h' : G t), ‖reflectedPairCoefficient r t E R (tailWeyl h) T v g h'‖ ≤
        C * Real.exp (-(M : ℝ) * rootPos (alpha g) + ((2 * d : ℕ) : ℝ) * ∑ j, |alpha g j|) *
          realMatrixHeight (wt t h') ^ d) :
    HasRectangularToralBound (((2 * d : ℕ) : ℝ) + ((2 * d : ℕ) : ℝ))
      (unequalDualPairCoefficient r t E R h T v) := by
  let N₀ : ℕ := 2 * d
  let A₀ : ℝ := (N₀ : ℝ) + N₀
  let B₀ : ℝ := (N₀ : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ))
  change HasRectangularToralBound A₀ (unequalDualPairCoefficient r t E R h T v)
  apply hasRectangularToralBound_of_log_bound (B := B₀)
  intro M
  obtain ⟨C, hC, hb⟩ := hToral (((t + 1) + 2 * (t + 1) * (r - (t + 1))) * M)
  let C' : ℝ := (2 * ((t : ℝ) + 1) ^ 2) ^ d
  refine ⟨C * C', mul_nonneg hC (by positivity), fun y k x => ?_⟩
  let g := torus y * k.val
  have hH := reflectedHeight_torus_mul_pow_le y k d
  have hExp := rectangular_toralExponent_le h M N₀ y k x
  change ‖reflectedPairCoefficient r t E R (tailWeyl h) T v (rect h g x) g‖ ≤ _
  refine (hb (rect h g x) g).trans ?_
  refine (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hC) hH
    (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg _) _) (by positivity)).trans_eq ?_
  rw [show ∀ u v : ℝ, (C * u) * (C' * v) = C * C' * (u * v) by intros; ring, ← Real.exp_add]
  congr 2
  dsimp only [A₀, B₀, N₀]
  ring

/-- The reflected rectangular integrals are absolutely convergent and holomorphic on one
right half-plane for all genuine smooth vectors of an opposite-character pair. -/
def RealPairedUnequalDualConvergenceStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (h : t < r) (a : ℝˣ) (T : D →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    ∀ μ : RealQuotientMeasureData t,
      ∃ σ : ℝ, ∀ v : D,
        (∀ s : ℂ, σ < s.re → Integrable (unequalPairedDualKernel r t E R h T v s)
          (realUnequalDualMeasure (r := r) a μ)) ∧
        DifferentiableOn ℂ (fun s => ∫ p, unequalPairedDualKernel r t E R h T v s p
          ∂(realUnequalDualMeasure (r := r) a μ)) {s | σ < s.re}

set_option maxHeartbeats 900000 in
theorem realPairedUnequalDualConvergence : RealPairedUnequalDualConvergenceStatement r t E R := by
  intro hR h a T hCov μ
  let w : G r := tailWeyl h
  obtain ⟨d, hToral⟩ := reflectedPairCoefficient_gauge r t E R hR w (unfoldingWeyl_mem_unitary h) a T hCov
  let N₀ : ℕ := 2 * d
  let A₀ : ℝ := (N₀ : ℝ) + N₀
  let c : ℝ := ((r - t : ℕ) : ℝ) / 2
  obtain ⟨σ, hConv⟩ := realRectangularToralConvergence t (r - (t + 1)) μ (realSelfDualMeasure a) A₀ c
    (by positivity)
  refine ⟨σ, fun v => ?_⟩
  let F := unequalDualPairCoefficient r t E R h T v
  let point (p : G t × Rect r t) : G r × G t := (rect h p.1 p.2, p.1)
  have hPoint : Continuous point := (continuous_rectangularPoint h).prodMk continuous_fst
  have hF : Continuous F := by
    change Continuous ((fun p : G r × G t => reflectedPairCoefficient r t E R w T v p.1 p.2) ∘ point)
    exact (continuous_reflectedPairCoefficient r t E R w T v).comp hPoint
  have hFInv := unequalDualPairCoefficient_invariant r t E R h a T hCov v
  have hBound := unequalDualPairCoefficient_toralBound r t E R h T v d (hToral v)
  have h' := hConv F hF hFInv hBound
  have e (s : ℂ) : unequalPairedDualKernel r t E R h T v s = fun p =>
      F (p.1.out, p.2) * Complex.exp ((s - c) * (logDet p.1.out : ℂ)) := by
    unfold c
    push_cast
    rfl
  simp only [← e] at h'
  exact h'

section Equal

variable (m : ℕ) (F : Fin 2 → Type*) [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
  (S : ∀ i, G (pairRanks m m i) →* (F i →L[ℂ] F i))

local notation "ranks" => pairRanks m m
local notation "M₀" => fun i => Mat (ranks i)
local notation "J" => 𝓘(ℝ, (∀ i : Fin 2, M₀ i))
local notation "Joint" => DerivativeSmoothVectors J (productAction M₀ S)
local notation "Separate" => fun i => DerivativeSmoothVectors 𝓘(ℝ, M₀ i) (S i)
local notation "SmoothAct" => DerivativeSmoothVectors.representation J (productAction M₀ S)
local notation "last" => Langlands.RankinSelberg.lastRow

/-- The reflected equal-rank kernel uses the Fourier transform of the same Schwartz row. -/
def equalPairedDualKernel (b : ℝˣ) (T : Joint →L[ℂ] ℂ) (v : Joint) (Φ : 𝓢(Row m, ℂ)) (s : ℂ) (q : Q m) : ℂ :=
  reflectedPairCoefficient m m F S 1 T v q.out q.out * realFourierTransform b Φ (last q.out) *
    ArchimedeanLocal.detPower realNormalizedAbs q.out s

/-- The reflected equal-rank kernel on a pure pair is the usual scalar dual kernel. -/
theorem equalPairedDualKernel_pure (b : ℝˣ) (T : Joint →L[ℂ] ℂ) (L : ∀ i, Separate i →L[ℂ] ℂ)
    (hT : ∀ v : ∀ i, Separate i, T (pureSmooth M₀ S v) = ∏ i, L i (v i))
    (v : ∀ i, Separate i) (Φ : 𝓢(Row m, ℂ)) (s : ℂ) :
    equalPairedDualKernel m F S b T (pureSmooth M₀ S v) Φ s = realEqualIntegrand
      (ArchimedeanLocal.dualFunction (m + 1) (slotCoefficient ranks S L v 0))
      (ArchimedeanLocal.dualFunction (m + 1) (slotCoefficient ranks S L v 1)) (realFourierTransform b Φ) s := by
  funext q
  unfold equalPairedDualKernel
  rw [reflectedPairCoefficient_pure m m F S _ T L hT, mul_one]
  rfl

variable [∀ i, CompleteSpace (F i)]

/-- A common initial half-plane for the reflected equal-rank integrals on genuine smooth pairs. -/
def RealPairedEqualDualConvergenceStatement : Prop :=
  (∀ i, IsContinuousRepresentation (S i)) →
  ∀ (a b : ℝˣ) (T : Joint →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (ranks i)) (v : Joint), T (SmoothAct (slot ranks i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    ∀ μ : RealQuotientMeasureData m,
      ∃ σ : ℝ, ∀ (v : Joint) (Φ : 𝓢(Row m, ℂ)),
        (∀ s : ℂ, σ < s.re → Integrable (equalPairedDualKernel m F S b T v Φ s) μ.measure) ∧
        DifferentiableOn ℂ (fun s => ∫ q, equalPairedDualKernel m F S b T v Φ s q ∂μ.measure) {s | σ < s.re}

set_option maxHeartbeats 900000 in
theorem realPairedEqualDualConvergence : RealPairedEqualDualConvergenceStatement m F S := by
  intro hS a b T hCov μ
  obtain ⟨d, hToral⟩ := reflectedPairCoefficient_gauge m m F S hS 1 (K m).one_mem a T hCov
  let growth : ℝ := ((2 * d : ℕ) : ℝ) + ((2 * d : ℕ) : ℝ)
  have hGrowth : 0 ≤ growth := by positivity
  obtain ⟨σ, hConv⟩ := exists_convergence_of_toral_bound μ hGrowth 0
  refine ⟨σ, fun v Φ => ?_⟩
  let W := reflectedPairCoefficient m m F S 1 T v
  let K₀ (g : G m) := W g g * realFourierTransform b Φ (last g)
  obtain ⟨hΦc, hΦ⟩ := fourier_rapidDecay b Φ
  have hRow : Continuous (last : G m → Row m) :=
    continuous_pi fun i => (Langlands.GeneralLinear.entry (Fin.last m) i).continuous
  have hW : Continuous (fun g => W g g) := by
    let diag (g : G m) : G m × G m := (g, g)
    have hDiag : Continuous diag := continuous_id.prodMk continuous_id
    change Continuous ((fun p : G m × G m => reflectedPairCoefficient m m F S 1 T v p.1 p.2) ∘ diag)
    exact (continuous_reflectedPairCoefficient m m F S 1 T v).comp hDiag
  have hK₀ : Continuous K₀ := hW.mul (hΦc.comp hRow)
  have hInv (u : N m) (g : G m) : K₀ (u.val * g) = K₀ g := by
    have hV := reflectedPairCoefficient_mul m m F S 1 T a hCov v
    have hChar : realWhittakerCharacter (-a) u.val * realWhittakerCharacter a u.val = 1 :=
      by simpa only [neg_neg] using realWhittakerCharacter_mul_neg (-a) u.val
    unfold K₀ W
    rw [hV.1 u, hV.2 u, ← mul_assoc, hChar, one_mul, Langlands.RankinSelberg.lastRow_unipotent_mul]
  have hBound : HasOrdinaryToralBound growth K₀ := by
    intro M
    obtain ⟨C, hC, hb⟩ := hToral v M
    obtain ⟨Cφ, hCφ, hDecay⟩ := exists_norm_le_exp hΦ (c := (m : ℝ) + 1) (by positivity) M
    let C' : ℝ := (2 * ((m : ℝ) + 1) ^ 2) ^ d
    refine ⟨C * C' * Cφ, mul_nonneg (mul_nonneg hC (by positivity)) hCφ, fun y k => ?_⟩
    let g := torus y * k.val
    have hV := hb g g
    change ‖W g g‖ ≤ _ at hV
    have he : alpha g = y := alpha_torus_mul_unitary y k
    rw [he] at hV
    have hh := reflectedHeight_torus_mul_pow_le y k d
    have hRowDecay := hDecay (last g) (y (Fin.last m)) (exp_le_mul_norm_lastRow y k)
    change ‖W g g * realFourierTransform b Φ (last g)‖ ≤ _
    rw [norm_mul]
    refine (mul_le_mul (hV.trans (mul_le_mul_of_nonneg_left hh (by positivity))) hRowDecay
      (norm_nonneg _) (by positivity)).trans_eq ?_
    rw [show ∀ x y z : ℝ, C * x * (C' * y) * (Cφ * z) = C * C' * Cφ * (x * y * z) by
      intros; ring, ← Real.exp_add, ← Real.exp_add]
    congr 2
    dsimp only [growth]
    ring
  have hs := hConv K₀ hK₀ hInv hBound
  have e (s : ℂ) : equalPairedDualKernel m F S b T v Φ s =
      fun q => K₀ q.out * Complex.exp (s * (logDet q.out : ℂ)) := rfl
  simp only [Complex.ofReal_zero, sub_zero, ← e] at hs
  exact hs

end Equal

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
