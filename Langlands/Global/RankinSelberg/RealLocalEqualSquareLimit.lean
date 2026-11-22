import Langlands.Global.RankinSelberg.RealLocalEqualFiniteSquareChambers
import Langlands.Global.RankinSelberg.RealOrthogonalSchwartzDensity
import Langlands.Analysis.Complex.AffineStripExtension
import Langlands.Global.Factors.CuspidalPairEpsilonComparisonData

/-! # The real equal-rank normalized unfolded integral for every square Schwartz test -/

noncomputable section

open Filter MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped NNReal SchwartzMap Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)
open RealJacquet (HasRealPairNormalizedGrowth exists_tendsto_realOrthogonalFiniteSchwartz)
open RealUniformWhittakerDual (dualCharacterBlocks realUniformWhittakerCharacterDual)
open RealLocalWhittaker (regularFunctions)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedAddCommGroup (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedSpace ℂ (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedSpace

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "gap" => Nat.lt_succ_self t

/-! ### Auxiliary estimates -/

private theorem uniformModel_regular {r : ℕ} (ds : List RealBlock) (a : ℝˣ)
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : W ∈ realUniformWhittakerModel r ds a) :
    Continuous W ∧ RealEqualConvergence.HasGauge W ∧
      ∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) (g : Langlands.GeneralLinear (r + 1) ℝ),
        ‖W (u.val * g)‖ = ‖W g‖ := by
  obtain ⟨hWreg, hWgrowth⟩ := realUniformWhittakerRegularity r ds a W hW
  have hWr : W ∈ regularFunctions r a := hWreg []
  refine ⟨hWr.2.1.continuous, RealWhittakerGauge.exists_gauge_bound hWreg hWgrowth, ?_⟩
  intro u g
  rw [hWr.1 u.val u.2 g, norm_mul, RealUnequalPairConvergence.norm_realWhittakerCharacter, one_mul]

private theorem continuous_realRectangularSchwartzFourier (b : ℝˣ) :
    Continuous (realRectangularSchwartzFourier b : 𝓢(Y, ℂ) → 𝓢(Y, ℂ)) := by
  have h : (realRectangularSchwartzFourier b : 𝓢(Y, ℂ) → 𝓢(Y, ℂ)) =
      ⇑((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (rectangularCoordinates (r := t + 2) (s := t + 2)).symm).comp
        ((scaledEuclideanFourierCLM b).comp
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (rectangularCoordinates (r := t + 2) (s := t + 2))))) := rfl
  rw [h]
  exact ContinuousLinearMap.continuous _

/-- The real pair `ε`-factor has bounded inverse on every vertical strip. -/
private theorem exists_norm_inv_realPairEpsilon_le (xs ys : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.re| ≤ M →
      ‖((realPairEpsilon xs ys b c hc w : ℂ))⁻¹‖ ≤ C := by
  let k : ℝ := ((realRank xs * realRank ys : ℕ) : ℝ)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  let e₀ : ℂ := (realPairEpsilon xs ys b c hc 0 : ℂ)
  have he₀ : e₀ ≠ 0 := (realPairEpsilon xs ys b c hc 0).ne_zero
  have hb : 0 < |(b : ℝ)| := abs_pos.mpr b.ne_zero
  refine ⟨‖e₀‖⁻¹ * Real.exp (abs (Real.log |(b : ℝ)|) * (k * M)), by positivity, fun w hw => ?_⟩
  rw [realPairEpsilon_eq_at_zero_mul_cpow, mul_inv, norm_mul, ← Complex.cpow_neg]
  change ‖e₀⁻¹‖ * _ ≤ _
  rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hb]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
  have hre : (-(((realRank xs * realRank ys : ℕ) : ℂ) * w)).re = -(k * w.re) := by
    simp [k]
  rw [hre, Real.rpow_def_of_pos hb]
  refine Real.exp_le_exp.mpr ?_
  have h1 : Real.log |(b : ℝ)| * -(k * w.re) ≤ abs (Real.log |(b : ℝ)|) * |k * w.re| := by
    rw [← abs_neg (k * w.re)]
    exact (le_abs_self _).trans (abs_mul _ _).le
  have h2 : |k * w.re| ≤ k * M := by
    rw [abs_mul, abs_of_nonneg hk]
    exact mul_le_mul_of_nonneg_left hw hk
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))

private theorem eventually_weight_sub {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X} {Ψ : ℕ → X} (hΨ : Tendsto Ψ atTop (𝓝 Φ))
    {p : X → ℝ} (hp : Continuous p) (hp₀ : p 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → p (Ψ i - Ψ j) ≤ ε := by
  have ht : Tendsto (fun q : ℕ × ℕ => Ψ q.1 - Ψ q.2) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using
      (hΨ.comp tendsto_fst).sub (hΨ.comp tendsto_snd)
  have h' := hp.continuousAt.tendsto.comp ht
  rw [hp₀] at h'
  have he := h'.eventually (eventually_lt_nhds hε)
  rw [prod_atTop_atTop_eq] at he
  obtain ⟨⟨i₀, j₀⟩, h⟩ := eventually_atTop.mp he
  exact ⟨max i₀ j₀, fun i j hi hj =>
    (h (i, j) ⟨(le_max_left _ _).trans hi, (le_max_right _ _).trans hj⟩).le⟩

private theorem tendsto_of_trace_bound {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X} {Ψ : ℕ → X} (hΨ : Tendsto Ψ atTop (𝓝 Φ))
    {p : X → ℝ} (hp : Continuous p) (hp₀ : p 0 = 0)
    {J : X → ℂ} {C : ℝ} (hJ : ∀ x y, ‖J x - J y‖ ≤ p (x - y) * C) :
    Tendsto (fun i => J (Ψ i)) atTop (𝓝 (J Φ)) := by
  have ht : Tendsto (fun i => Ψ i - Φ) atTop (𝓝 0) := by
    simpa only [sub_self] using hΨ.sub (tendsto_const_nhds (x := Φ))
  have h' := (hp.continuousAt.tendsto.comp ht).mul_const C
  rw [hp₀, zero_mul] at h'
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun i => hJ (Ψ i) Φ) h')

private theorem tilt_exponential_bound {ε δ K₀ L₀ K L : ℝ} {v s z t : ℂ}
    (hε : 0 ≤ ε) (hδ : δ ≤ ε) (hL₀ : 0 ≤ L₀)
    (hK : K₀ + L₀ ≤ K) (hL : L₀ ≤ L)
    (ht : |t.im| = |s.im|) (hz : |z.im| ≤ |v.im| + |s.im|) :
    δ * Real.exp (K₀ * |t.im| + L₀ * |z.im|) ≤
      ε * Real.exp (K * |s.im| + L * |v.im|) := by
  rw [ht]
  refine mul_le_mul hδ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hε
  linarith [mul_le_mul_of_nonneg_left hz hL₀, mul_le_mul_of_nonneg_right hK (abs_nonneg s.im),
    mul_le_mul_of_nonneg_right hL (abs_nonneg v.im)]

/-! ### The square limit -/

variable (t) in
/-- For every square Schwartz test `Ψ` there is one function `A` of `(z, s)`, holomorphic
along every holomorphic curve and of exponential growth on vertical strips in `s`, whose
trace on a primal chamber is the real unfolded equal-rank integral times the two reciprocal
`L`-factors, and whose reflection `s ↦ 1 - s`, multiplied by the two `ε`-factors and signs,
has trace on a dual chamber equal to the dual unfolded integral (Fourier test, duals, inverse
character) times the two dual reciprocal `L`-factors. The chambers do not depend on `Ψ`. The
inputs are those of `RealLocalEqualFiniteSquareChambersStatement`, nonzero signs, and the
matrix input for every orthogonal-finite square test. -/
def RealLocalEqualSquareLimitStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (e : Fin 2)
    (cs fs : List RealCharacterData), cs.length = t + 1 → fs.length = t + 2 →
  ∀ (W : G → ℂ), W ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a →
  ∀ (B : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    (∃ L : DerivativeSmoothVectors (matrixModel ℝ (t + 2))
        (RealStandardCompactBanach.representation (n := t + 2) (fs.map RealBlock.character)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation (fs.map RealBlock.character) (-a) B L) →
  ∀ (f : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character))
    (xs ys xsd ysd : List RealBlock) (bA : ℝˣ) (cA : ℝ≥0) (hcA : 0 < cA) (signA : ℂ),
    signA ≠ 0 →
    (∀ V ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a),
      HasRealPairNormalizedGrowth xs ys xsd ysd bA cA hcA signA
        (realUnequalIntegral gap D V W) (realUnequalDualIntegral gap (-a) D V W)) →
  ∀ (us vs usd vsd : List RealBlock) (bM : ℝˣ) (cM : ℝ≥0) (hcM : 0 < cM) (signM : ℂ),
    signM ≠ 0 →
    (∀ Φ : 𝓢(Y, ℂ), FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ (t + 2) =>
        fun X : Y => Φ (k.val⁻¹.val * X))) →
      RealMatrixCoefficientNormalizedGrowth t D' a e (fs.map RealBlock.character) f Φ
        us vs usd vsd bM cM hcM signM) →
    ∃ τ σ τd σd : ℝ, ∀ Ψ : 𝓢(Y, ℂ), ∃ A : ℂ × ℂ → ℂ,
      (∀ γ : ℂ → ℂ × ℂ, Differentiable ℂ γ → Differentiable ℂ (A ∘ γ)) ∧
      (∀ z : ℂ, HasStripExponentialGrowth (fun s => A (z, s))) ∧
      (∀ z s : ℂ, τ < z.re → σ < s.re →
        A (z, s) = (realPairLFactor xs ys).denominator s *
          (realPairLFactor us vs).denominator (s + z) *
          ∫ p, equalUnfoldedKernel (charData e z) Ψ W (B f) s p ∂(D.measure.prod D'.groupHaar)) ∧
      (∀ z s : ℂ, τd < (-z).re → σd < s.re →
        signA * (realPairEpsilon xs ys bA cA hcA (1 - s) : ℂ) *
            (signM * (realPairEpsilon us vs bM cM hcM (1 - s + z) : ℂ)) * A (z, 1 - s) =
          (realPairLFactor xsd ysd).denominator s *
            (realPairLFactor usd vsd).denominator (s - z) *
            ∫ p, equalUnfoldedKernel (charData e (-z)) (realRectangularSchwartzFourier (-a) Ψ)
              (ArchimedeanLocal.dualFunction (t + 1) W)
              (ArchimedeanLocal.dualFunction (t + 2) (B f)) s p ∂(D.measure.prod D'.groupHaar))

set_option maxHeartbeats 2000000 in
theorem realLocalEqualSquareLimit : RealLocalEqualSquareLimitStatement t := by
  intro D D' a e cs fs hcs hfs W hW B hB hL f xs ys xsd ysd bA cA hcA signA hsA hAdj
    us vs usd vsd bM cM hcM signM hsM hMat
  have hV : B f ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hWd := realUniformWhittakerCharacterDual t cs hcs a W hW
  have hVd := realUniformWhittakerCharacterDual (t + 1) fs hfs (-a) (B f) hV
  obtain ⟨hWc, hWg, -⟩ := uniformModel_regular _ _ hW
  obtain ⟨hVc, hVg, hVu⟩ := uniformModel_regular _ _ hV
  obtain ⟨hWdc, hWdg, -⟩ := uniformModel_regular _ _ hWd
  obtain ⟨hVdc, hVdg, hVdu⟩ := uniformModel_regular _ _ hVd
  obtain ⟨τ, σ, τd, σd, -, -, hfin⟩ := realLocalEqualFiniteSquareChambers D D' a e cs fs hcs hfs
    W hW B hB hL f xs ys xsd ysd bA cA hcA signA hAdj us vs usd vsd bM cM hcM signM
  let dA := (realPairLFactor xs ys).denominator
  let dM := (realPairLFactor us vs).denominator
  let dAd := (realPairLFactor xsd ysd).denominator
  let dMd := (realPairLFactor usd vsd).denominator
  let Wd := ArchimedeanLocal.dualFunction (t + 1) W
  let Vd := ArchimedeanLocal.dualFunction (t + 2) (B f)
  obtain ⟨α, β, hp⟩ := exists_equalNormalizedTrace_bound D D' hWc hVc hWg hVg hVu e
    (realPairLFactor xs ys).entire.continuous (stripGrowth_realPairLFactor_denominator xs ys)
    (realPairLFactor us vs).entire.continuous (stripGrowth_realPairLFactor_denominator us vs) 1
  obtain ⟨αd, βd, hq⟩ := exists_equalNormalizedTrace_bound D D' hWdc hVdc hWdg hVdg hVdu e
    (realPairLFactor xsd ysd).entire.continuous (stripGrowth_realPairLFactor_denominator xsd ysd)
    (realPairLFactor usd vsd).entire.continuous (stripGrowth_realPairLFactor_denominator usd vsd) 1
  let primalShift := max τ α
  let primalSpectral := max σ β
  let dualShift := max τd αd
  let dualSpectral := max σd βd
  refine ⟨primalShift, primalSpectral, dualShift, dualSpectral, fun Ψ => ?_⟩
  let T : 𝓢(Y, ℂ) → 𝓢(Y, ℂ) := realRectangularSchwartzFourier (-a)
  obtain ⟨Φ, hΦfin, hΦ⟩ := exists_tendsto_realOrthogonalFiniteSchwartz Ψ
  have hΦd : Tendsto (fun j => T (Φ j)) atTop (𝓝 (T Ψ)) :=
    ((continuous_realRectangularSchwartzFourier (-a)).tendsto Ψ).comp hΦ
  choose F Fd hF hFd hg hgT _ _ hPlus hMinus hRef using
    fun j : ℕ => hfin (Φ j) (hΦfin j) (hMat (Φ j) (hΦfin j))
  let P := equalNormalizedTrace D D' e dA dM 1 W (B f)
  let Q := equalNormalizedTrace D D' e dAd dMd 1 Wd Vd
  let Ph (z s : ℂ) : ℂ := signA * (realPairEpsilon xs ys bA cA hcA s : ℂ) *
    (signM * (realPairEpsilon us vs bM cM hcM (s + z) : ℂ))
  have hPh (z s : ℂ) : Ph z s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsA (realPairEpsilon xs ys bA cA hcA s).ne_zero)
      (mul_ne_zero hsM (realPairEpsilon us vs bM cM hcM (s + z)).ne_zero)
  have hPe (Ψ' : 𝓢(Y, ℂ)) (z s : ℂ) : P Ψ' z s = dA s * dM (s + z) *
      ∫ p, equalUnfoldedKernel (charData e z) Ψ' W (B f) s p ∂(D.measure.prod D'.groupHaar) := by
    simp only [P, equalNormalizedTrace, one_mul]
  have hQe (Ψ' : 𝓢(Y, ℂ)) (z s : ℂ) : Q Ψ' (-z) s = dAd s * dMd (s - z) *
      ∫ p, equalUnfoldedKernel (charData e (-z)) Ψ' Wd Vd s p ∂(D.measure.prod D'.groupHaar) := by
    simp only [Q, equalNormalizedTrace, one_mul, sub_eq_add_neg]
  have hP (j : ℕ) (z s : ℂ) (hz : τ < z.re) (hs : σ < s.re) : F j (z, s) = P (Φ j) z s := by
    rw [hPlus j z s hz hs, hPe]
  have hQ (j : ℕ) (z s : ℂ) (hz : τd < (-z).re) (hs : σd < s.re) :
      Fd j (z, s) = Q (T (Φ j)) (-z) s := by
    rw [hMinus j z s hz hs, hQe]
  have hInv (j : ℕ) (z s : ℂ) : F j (z, s) = (Ph z s)⁻¹ * Fd j (z, 1 - s) := by
    rw [hRef j z s, ← mul_assoc, inv_mul_cancel₀ (hPh z s), one_mul]
  have hLines : ∀ R a b : ℝ, 0 ≤ R → a ≤ b → ∃ l u K L : ℝ, l < a ∧ b < u ∧ 0 ≤ L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
        ∀ v s : ℂ, |v.re| ≤ R → s.re = l ∨ s.re = u →
          ‖F i (v + s, s) - F j (v + s, s)‖ ≤ ε * Real.exp (K * |s.im| + L * |v.im|) := by
    intro R a b hR _
    let l := min a (min (1 - dualSpectral) (-dualShift - R)) - 1
    let u := max b (max primalSpectral (primalShift + R)) + 1
    have hl : l < a := by
      dsimp only [l]
      linarith [min_le_left a (min (1 - dualSpectral) (-dualShift - R))]
    have hu : b < u := by
      dsimp only [u]
      linarith [le_max_left b (max primalSpectral (primalShift + R))]
    have hlu : primalShift < u - R := by
      dsimp only [u]
      linarith [(le_max_right primalSpectral (primalShift + R)).trans (le_max_right b _)]
    have hsu : primalSpectral < u := by
      dsimp only [u]
      linarith [(le_max_left primalSpectral (primalShift + R)).trans (le_max_right b _)]
    have hll : dualShift < -R - l := by
      dsimp only [l]
      linarith [(min_le_right a _).trans (min_le_right (1 - dualSpectral) (-dualShift - R))]
    have hsl : dualSpectral < 1 - l := by
      dsimp only [l]
      linarith [(min_le_right a _).trans (min_le_left (1 - dualSpectral) (-dualShift - R))]
    obtain ⟨Kp, Lp, pp, _, hLp, hpp, hpp₀, hbp⟩ := hp (u - R) (u + R) u
      ((le_max_right τ α).trans_lt hlu).le ((le_max_right σ β).trans_lt hsu)
    obtain ⟨Km, Lm, pm, _, hLm, hpm, hpm₀, hbm⟩ := hq (-R - l) (R - l) (1 - l)
      ((le_max_right τd αd).trans_lt hll).le ((le_max_right σd βd).trans_lt hsl)
    obtain ⟨CA, hCA, hεA⟩ := exists_norm_inv_realPairEpsilon_le xs ys bA cA hcA (|l| + 2 * |l| + R)
    obtain ⟨CM, hCM, hεM⟩ := exists_norm_inv_realPairEpsilon_le us vs bM cM hcM (|l| + 2 * |l| + R)
    let Cph := ‖signA⁻¹‖ * CA * (‖signM⁻¹‖ * CM)
    have hCph : 0 ≤ Cph := by positivity
    have hPhb (v s : ℂ) (hv : |v.re| ≤ R) (hs : s.re = l) : ‖(Ph (v + s) s)⁻¹‖ ≤ Cph := by
      have h1 : |s.re| ≤ |l| + 2 * |l| + R := by
        rw [hs]
        linarith [abs_nonneg l, hR]
      have h2 : |(s + (v + s)).re| ≤ |l| + 2 * |l| + R := by
        rw [Complex.add_re, Complex.add_re, hs]
        calc |l + (v.re + l)| ≤ |l| + |v.re + l| := abs_add_le _ _
          _ ≤ |l| + (|v.re| + |l|) := add_le_add le_rfl (abs_add_le _ _)
          _ ≤ |l| + 2 * |l| + R := by linarith [abs_nonneg l]
      simp only [Ph, mul_inv, norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hεA s h1) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hεM _ h2) (norm_nonneg _)) (by positivity)
        (mul_nonneg (norm_nonneg _) hCA)
    refine ⟨l, u, max (Kp + Lp) (Km + Lm), max Lp Lm, hl, hu, hLp.trans (le_max_left _ _), ?_⟩
    intro ε hε
    obtain ⟨Np, hNp⟩ := eventually_weight_sub hΦ hpp hpp₀ hε
    have hδ : 0 < ε / (Cph + 1) := div_pos hε (by linarith)
    obtain ⟨Nm, hNm⟩ := eventually_weight_sub hΦd hpm hpm₀ hδ
    have hCδ : Cph * (ε / (Cph + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    refine ⟨max Np Nm, fun i j hi hj v s hv hs => ?_⟩
    obtain ⟨hvl, hvu⟩ := abs_le.mp hv
    rcases hs with hs | hs
    · let z := v + s
      have hzr₁ : -R - l ≤ (-z).re := by
        simp only [z, Complex.neg_re, Complex.add_re, hs]
        linarith
      have hzr₂ : (-z).re ≤ R - l := by
        simp only [z, Complex.neg_re, Complex.add_re, hs]
        linarith
      have htr : (1 - s).re = 1 - l := by simp only [Complex.sub_re, Complex.one_re, hs]
      have hzτ : τd < (-z).re := ((le_max_left _ _).trans_lt hll).trans_le hzr₁
      have htσ : σd < (1 - s).re := htr ▸ (le_max_left _ _).trans_lt hsl
      have hti : |(1 - s).im| = |s.im| := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      have hzi : |(-z).im| ≤ |v.im| + |s.im| := by
        simp only [z, Complex.neg_im, abs_neg, Complex.add_im]
        exact abs_add_le _ _
      change ‖F i (z, s) - F j (z, s)‖ ≤ _
      rw [hInv i z s, hInv j z s, ← mul_sub, norm_mul, hQ i z (1 - s) hzτ htσ,
        hQ j z (1 - s) hzτ htσ]
      have hw := hNm i j ((le_max_right _ _).trans hi) ((le_max_right _ _).trans hj)
      calc ‖(Ph z s)⁻¹‖ * ‖Q (T (Φ i)) (-z) (1 - s) - Q (T (Φ j)) (-z) (1 - s)‖
          ≤ Cph * (pm (T (Φ i) - T (Φ j)) * Real.exp (Km * |(1 - s).im| + Lm * |(-z).im|)) :=
            mul_le_mul (hPhb v s hv hs) (hbm (T (Φ i)) (T (Φ j)) (-z) (1 - s) hzr₁ hzr₂ htr)
              (norm_nonneg _) hCph
        _ ≤ (Cph * (ε / (Cph + 1))) * Real.exp (Km * |(1 - s).im| + Lm * |(-z).im|) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hCph)
              (Real.exp_pos _).le
        _ ≤ ε * Real.exp (max (Kp + Lp) (Km + Lm) * |s.im| + max Lp Lm * |v.im|) :=
            tilt_exponential_bound hε.le hCδ hLm (le_max_right _ _) (le_max_right _ _) hti hzi
    · let z := v + s
      have hzr₁ : u - R ≤ z.re := by simp only [z, Complex.add_re, hs]; linarith
      have hzr₂ : z.re ≤ u + R := by simp only [z, Complex.add_re, hs]; linarith
      have hzτ : τ < z.re := ((le_max_left _ _).trans_lt hlu).trans_le hzr₁
      have hsσ : σ < s.re := hs ▸ (le_max_left _ _).trans_lt hsu
      have hzi : |z.im| ≤ |v.im| + |s.im| := by
        simp only [z, Complex.add_im]
        exact abs_add_le _ _
      change ‖F i (z, s) - F j (z, s)‖ ≤ _
      rw [hP i z s hzτ hsσ, hP j z s hzτ hsσ]
      exact (hbp (Φ i) (Φ j) z s hzr₁ hzr₂ hs).trans
        (tilt_exponential_bound hε.le (hNp i j ((le_max_left _ _).trans hi)
          ((le_max_left _ _).trans hj)) hLp (le_max_left _ _) (le_max_left _ _) rfl hzi)
  obtain ⟨A, hA, hCurve, hGrowth⟩ := Langlands.Analysis.affineStripExtension F hF hg hgT hLines
  have hlim (p : ℂ × ℂ) : Tendsto (fun j => F j p) atTop (𝓝 (A p)) :=
    hA.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ p)
  refine ⟨A, hCurve, hGrowth, fun z s hz hs => ?_, fun z s hz hs => ?_⟩
  · obtain ⟨_, _, p, _, _, hpcont, hp₀, hb⟩ := hp z.re z.re s.re
      ((le_max_right _ _).trans_lt hz).le ((le_max_right _ _).trans_lt hs)
    have hlimP := tendsto_of_trace_bound hΦ hpcont hp₀
      (fun Φ₁ Φ₂ => hb Φ₁ Φ₂ z s le_rfl le_rfl rfl)
    have h := tendsto_nhds_unique (hlim (z, s)) (hlimP.congr fun j =>
      (hP j z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)).symm)
    exact h.trans (hPe Ψ z s)
  · obtain ⟨_, _, p, _, _, hpcont, hp₀, hb⟩ := hq (-z).re (-z).re s.re
      ((le_max_right _ _).trans_lt hz).le ((le_max_right _ _).trans_lt hs)
    have hlimQ := tendsto_of_trace_bound hΦd hpcont hp₀
      (fun Φ₁ Φ₂ => hb Φ₁ Φ₂ (-z) s le_rfl le_rfl rfl)
    have hFd (j : ℕ) : Fd j (z, s) = Ph z (1 - s) * F j (z, 1 - s) := by
      have h := hRef j z (1 - s)
      rwa [sub_sub_cancel] at h
    have hlimFd : Tendsto (fun j => Fd j (z, s)) atTop (𝓝 (Ph z (1 - s) * A (z, 1 - s))) := by
      simp only [hFd]
      exact (hlim (z, 1 - s)).const_mul _
    have h := tendsto_nhds_unique hlimFd (hlimQ.congr fun j =>
      (hQ j z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)).symm)
    exact h.trans (hQe (T Ψ) z s)

end Langlands.Global.RankinSelbergGlobal.RealGodement
