import Langlands.Global.RankinSelberg.RealMatrixPairIdentity
import Langlands.Global.RankinSelberg.ArchimedeanMellinPairPowerGrowth
import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth

/-! # Entire normalizations of strip growth for the real matrix zeta integrals

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Matrix Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData realRank realPairLFactor
  realPairEpsilon HasStripExponentialGrowth GammaBlock)
open Langlands.Archimedean.RealJacquetFrobenius (charData)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanMellinPair ArchimedeanDeterminantTheta RealSquareFourier
  RealPrincipalSeries

local instance realGrowthGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realGrowthGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩
local instance realGrowthMatrixSecondCountable (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
local instance realGrowthGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ
local notation "dp" => ArchimedeanLocal.detPower realNormalizedAbs

/-! ### The normalized growth property -/

/-- Two entire functions of exponential growth on vertical strips that agree, on a right
half-plane, with the two real matrix zeta integrals multiplied by the given factors. -/
def HasRealMatrixNormalizedGrowth (μ : Measure G) (f : G → ℂ) (Φ : Mat → ℂ) (fd : G → ℂ)
    (Φd : Mat → ℂ) (D Dd : ℂ → ℂ) : Prop :=
  ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
    ∀ s : ℂ, σ < s.re →
      N s = D s * realMatrixZeta μ f Φ s ∧ Nd s = Dd s * realMatrixZeta μ fd Φd s

namespace HasRealMatrixNormalizedGrowth

/-- The factors may be replaced by pointwise equal ones. -/
theorem congr_factor {μ : Measure G} {f : G → ℂ} {Φ : Mat → ℂ} {fd : G → ℂ} {Φd : Mat → ℂ}
    {D Dd D' Dd' : ℂ → ℂ} (h : HasRealMatrixNormalizedGrowth μ f Φ fd Φd D Dd)
    (hD : ∀ s, D s = D' s) (hDd : ∀ s, Dd s = Dd' s) :
    HasRealMatrixNormalizedGrowth μ f Φ fd Φd D' Dd' := by
  obtain ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hR⟩ := h
  exact ⟨σ, N, Nd, hN, hNd, hNg, hNdg, fun s hs => by rw [← hD, ← hDd]; exact hR s hs⟩

/-- Rescaling the Fourier parameter of the dual Schwartz function, when the dual coefficient has
the corresponding scalar equivariance, keeps the same factors. -/
theorem scale (μ : Measure G) [μ.IsHaarMeasure] (b : ℝˣ) (f fd : G → ℂ) (ω : ℂ)
    (hω : ∀ g : G, fd ((realMatrixScalar b)⁻¹ * g) = ω * fd g) (Φ : 𝓢(Mat, ℂ)) {D Dd : ℂ → ℂ}
    (h : HasRealMatrixNormalizedGrowth μ f Φ fd (matrixTransform 1 Φ) D Dd) :
    HasRealMatrixNormalizedGrowth μ f Φ fd (matrixTransform b Φ) D Dd := by
  obtain ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hR⟩ := h
  let c := realMatrixScaledDualFactor (r := r) b ω
  refine ⟨σ, N, fun s => c s * Nd s, hN, (differentiable_realMatrixScaledDualFactor b ω).mul hNd,
    hNg, (stripGrowth_realMatrixScaledDualFactor b ω).mul hNdg, fun s hs => ⟨(hR s hs).1, ?_⟩⟩
  show c s * Nd s = _
  rw [realMatrixZeta_scaled_dual μ b fd ω hω Φ s, (hR s hs).2]
  ring
where
  /-- The scaled dual factor is bounded on every vertical strip. -/
  stripGrowth_realMatrixScaledDualFactor (b : ℝˣ) (ω : ℂ) :
      HasStripExponentialGrowth (realMatrixScaledDualFactor (r := r) b ω) := by
    intro a a'
    set p : ℝ := |(b : ℝ)| with hpdef
    have hp : 0 < p := abs_pos.mpr b.ne_zero
    have hnorm (s : ℂ) : ‖realMatrixScaledDualFactor (r := r) b ω s‖ =
        ‖ω‖ * p ^ (((n : ℕ) : ℝ) * (1 / 2 - s.re)) := by
      rw [realMatrixScaledDualFactor, norm_mul]
      beta_reduce
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
      congr 2
      simp
    refine ⟨‖ω‖ * (p ^ (((n : ℕ) : ℝ) * (1 / 2 - a)) + p ^ (((n : ℕ) : ℝ) * (1 / 2 - a'))), 0, 0,
      by positivity, le_rfl, fun s hsa hsb _ => ?_⟩
    rw [hnorm, zero_mul, Real.exp_zero, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h0 := Real.rpow_nonneg hp.le (((n : ℕ) : ℝ) * (1 / 2 - a))
    have h0' := Real.rpow_nonneg hp.le (((n : ℕ) : ℝ) * (1 / 2 - a'))
    rcases le_or_gt 1 p with h1 | h1
    · have := Real.rpow_le_rpow_of_exponent_le h1
        (show ((n : ℕ) : ℝ) * (1 / 2 - s.re) ≤ ((n : ℕ) : ℝ) * (1 / 2 - a) from
          mul_le_mul_of_nonneg_left (by linarith) hn)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hp h1.le
        (show ((n : ℕ) : ℝ) * (1 / 2 - a') ≤ ((n : ℕ) : ℝ) * (1 / 2 - s.re) from
          mul_le_mul_of_nonneg_left (by linarith) hn)
      linarith

/-- Multiplying the primal coefficient by `|det|^w` and the dual one by `|det|^(-w)` translates
the normalizations and the factors by `w` and `-w`. -/
theorem shift (μ : Measure G) {F Fd F' Fd' : G → ℂ} {Φ Φd : Mat → ℂ} (w : ℂ)
    (hF : ∀ g, F' g = dp g w * F g) (hFd : ∀ g, Fd' g = dp g (-w) * Fd g) {D Dd : ℂ → ℂ}
    (h : HasRealMatrixNormalizedGrowth μ F Φ Fd Φd D Dd) :
    HasRealMatrixNormalizedGrowth μ F' Φ Fd' Φd (fun s => D (s + w)) (fun t => Dd (t + -w)) := by
  obtain ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hR⟩ := h
  have hg {M : ℂ → ℂ} (hM : HasStripExponentialGrowth M) (v : ℂ) :
      HasStripExponentialGrowth (fun s => M (s + v)) := by
    simpa only [Complex.ofReal_one, div_one] using hM.div_add v (c := 1) one_pos
  refine ⟨σ + |w.re|, fun s => N (s + w), fun s => Nd (s + -w),
    hN.comp (differentiable_id.add_const w), hNd.comp (differentiable_id.add_const (-w)),
    hg hNg w, hg hNdg (-w), fun s hs => ?_⟩
  have h1 : σ < (s + w).re := by
    rw [Complex.add_re]
    linarith [neg_abs_le w.re]
  have h2 : σ < (s + -w).re := by
    rw [Complex.add_re, Complex.neg_re]
    linarith [le_abs_self w.re]
  rw [realMatrixZeta_shift μ Φ w hF s, realMatrixZeta_shift μ Φd (-w) hFd s]
  exact ⟨(hR _ h1).1, (hR _ h2).2⟩

end HasRealMatrixNormalizedGrowth

/-! ### The torus factors -/

theorem torusEpsilon_ne_zero {m : ℕ} (e : Fin m → Fin 2) : torusEpsilon e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ Complex.I_ne_zero

/-- The reciprocal of the torus `L`-product has exponential growth on vertical strips. -/
theorem stripGrowth_torusL_inv {m : ℕ} (e : Fin m → Fin 2) (u : Fin m → ℂ) :
    HasStripExponentialGrowth (fun s => (torusL e u s)⁻¹) := by
  have h := HasStripExponentialGrowth.finset_prod Finset.univ
    (fun i => (GammaBlock.real (u i + ((e i).val : ℂ))).factor.denominator)
    (fun i _ => (GammaBlock.real _).stripGrowth_denominator)
  convert h using 2 with s
  rw [torusL, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  change _ = (Complex.Gammaℝ (s + (u i + ((e i).val : ℂ))))⁻¹
  rw [add_assoc]

/-! ### Normalized growth along the matrix chain -/

/-- The determinant theta identity gives entire normalizations of strip growth, with the
reciprocal torus `L`-products as factors. -/
theorem realMatrixNormalizedGrowth_of_theta (μ : Measure G) [μ.IsHaarMeasure]
    (e : I → Fin 2) (u : I → ℂ) {f fd : G → ℂ} (hf : Continuous f) (hfd : Continuous fd)
    (Φ Φd : 𝓢(Mat, ℂ)) {C Cd : ℝ} {N Nd : ℕ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd)
    (hb : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N)
    (hbd : ∀ g, ‖fd g‖ ≤ Cd * realMatrixHeight g ^ Nd)
    (hθ : ∀ a : ℝ, 0 < a → theta μ (realMatrixBaseKernel f Φ) realMatrixDetScale (detH e u) a =
      (a : ℂ) * theta μ (realMatrixBaseKernel fd Φd) realMatrixDetScale (detK e u) a⁻¹) :
    HasRealMatrixNormalizedGrowth μ f Φ fd Φd (fun s => (torusL e u s)⁻¹)
      (fun s => (torusL e (-u) s)⁻¹) := by
  let T : ℝ := (n : ℝ) + 2 * max N Nd - (r : ℝ) / 2
  have ht (t : ℝ) (ht : T ≤ t) : (n : ℝ) + 2 * N ≤ t + (r : ℝ) / 2 := by
    have hN : (N : ℝ) ≤ ((max N Nd : ℕ) : ℝ) := by exact_mod_cast le_max_left N Nd
    dsimp [T] at ht
    linarith
  have htd (t : ℝ) (ht : T ≤ t) : (n : ℝ) + 2 * Nd ≤ t + (r : ℝ) / 2 := by
    have hNd : (Nd : ℝ) ≤ ((max N Nd : ℕ) : ℝ) := by exact_mod_cast le_max_right N Nd
    dsimp [T] at ht
    linarith
  obtain ⟨M, Md, hM, hMd, hMg, hMdg, hZ, hZd, -⟩ := mellinPairPowerNormalizedGrowth μ μ
    (realMatrixBaseKernel f Φ) realMatrixDetScale (realMatrixBaseKernel fd Φd) realMatrixDetScale
    (detH e u) (detK e u) T n (torusEpsilon e) (fun s => (torusL e u s)⁻¹)
    (fun s => (torusL e (-u) s)⁻¹)
    (measurable_realMatrixBaseKernel hf Φ.continuous).aestronglyMeasurable
    (measurable_realMatrixBaseKernel hfd Φd.continuous).aestronglyMeasurable
    measurable_realMatrixDetScale measurable_realMatrixDetScale realMatrixDetScale_pos
    realMatrixDetScale_pos (measurable_detH e u) (measurable_detK e u) (rapidDecay_detH e u)
    (rapidDecay_detK e u)
    (fun t ht' => integrable_realMatrixBaseKernel_power μ hf.measurable Φ hC hb (ht t ht'))
    (fun t ht' => integrable_realMatrixBaseKernel_power μ hfd.measurable Φd hCd hbd (htd t ht'))
    hθ (torusEpsilon_ne_zero e) (mellin_detH e u) (mellin_detK e u)
    (stripGrowth_torusL_inv e u) (stripGrowth_torusL_inv e (-u))
  refine ⟨T, M, Md, hM, hMd, hMg, hMdg, fun s hs => ⟨?_, ?_⟩⟩
  · rw [hZ s hs.le]
    simp only [realMatrixZeta, realMatrixZetaKernel_eq]
  · rw [hZd s hs.le]
    simp only [realMatrixZeta, realMatrixZetaKernel_eq]

/-- Normalized growth at the Fourier parameter one for the coefficients of a
compact-derivative-bounded linear form on a position principal series. -/
theorem realMatrixCompactNormalizedGrowthAtOne (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (Φ : 𝓢(Mat, ℂ)) :
    let e (i : I) := RealBlockPosition.realPositionSign ds i
    let u (i : I) := GramFormula.realPositionExponent ds i
    let F (g : G) := ℓ (translate r ds g f)
    HasRealMatrixNormalizedGrowth μ F Φ (F ∘ ιg) (matrixTransform 1 Φ)
      (fun s => (torusL e u s)⁻¹) (fun s => (torusL e (-u) s)⁻¹) := by
  intro e u F
  have hFc : Continuous F := continuous_compactFunctionalCoefficient ℓ hℓ f
  have hFdc : Continuous (F ∘ ιg) := hFc.comp (continuous_inverseTranspose n ℝ)
  obtain ⟨N, hN⟩ := compactFunctionalGrowth r ds ℓ hℓ
  obtain ⟨C, hC, hB⟩ := hN f
  have hBd (g : G) : ‖(F ∘ ιg) g‖ ≤ C * realMatrixHeight g ^ N := by
    simpa only [Function.comp_apply, realMatrixHeight_inverseTranspose] using hB (ιg g)
  exact realMatrixNormalizedGrowth_of_theta μ e u hFc hFdc Φ (matrixTransform 1 Φ) hC hC hB hBd
    (fun a ha => realMatrix_functional_theta_at_one μ κ ds f ℓ hℓ Φ (a := a) ha)

/-- Normalized growth at any nonzero Fourier parameter for the coefficients of a
compact-derivative-bounded linear form on a position principal series. -/
theorem realMatrixCompactNormalizedGrowth (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (Φ : 𝓢(Mat, ℂ)) (b : ℝˣ) :
    let e (i : I) := RealBlockPosition.realPositionSign ds i
    let u (i : I) := GramFormula.realPositionExponent ds i
    let F (g : G) := ℓ (translate r ds g f)
    HasRealMatrixNormalizedGrowth μ F Φ (F ∘ ιg) (matrixTransform b Φ)
      (fun s => (torusL e u s)⁻¹) (fun s => (torusL e (-u) s)⁻¹) := by
  intro e u F
  exact HasRealMatrixNormalizedGrowth.scale μ b F (F ∘ ιg) _
    (fun g => realMatrixFunctionalCoefficient_dual_scalar ds f ℓ b g) Φ
    (realMatrixCompactNormalizedGrowthAtOne μ κ ds f ℓ hℓ Φ)

/-- Normalized growth for the determinant-character twist of the coefficients of a
compact-derivative-bounded linear form, at any nonzero Fourier parameter. -/
theorem realMatrixTwistedNormalizedGrowth (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (c : RealCharacterData) (Φ : 𝓢(Mat, ℂ))
    (b : ℝˣ) :
    let e (i : I) := RealBlockPosition.realPositionSign ds i + c.parity
    let u (i : I) := GramFormula.realPositionExponent ds i + c.exponent
    let F (g : G) := realDetCharacter c g * ℓ (translate r ds g f)
    HasRealMatrixNormalizedGrowth μ F Φ (F ∘ ιg) (matrixTransform b Φ)
      (fun s => (torusL e u s)⁻¹) (fun s => (torusL e (-u) s)⁻¹) := by
  intro e u F
  let ds' := twistedPositionList n ds (charData c.parity 0)
  obtain ⟨f', ℓ', hℓ', hcoef⟩ := exists_signTwist_coefficient ds f ℓ hℓ c
  let F0 (g : G) := ℓ' (translate r ds' g f')
  have h0 := realMatrixCompactNormalizedGrowth (r := r) μ κ ds' f' ℓ' hℓ' Φ b
  have hF (g : G) : F g = dp g c.exponent * F0 g := hcoef g
  have hFd (g : G) : (F ∘ ιg) g = dp g (-c.exponent) * (F0 ∘ ιg) g := by
    change F (ιg g) = _ * F0 (ιg g)
    rw [hF, detPower_inverseTranspose]
  refine (HasRealMatrixNormalizedGrowth.shift μ c.exponent hF hFd h0).congr_factor
    (fun s => ?_) (fun s => ?_)
  · exact congrArg (·⁻¹) (torusL_signTwist_shift (r := r) ds c s)
  · have h := torusL_neg_signTwist_shift (r := r) ds c s
    rw [sub_eq_add_neg] at h
    exact congrArg (·⁻¹) h

/-! ### The pair form -/

/-- For the determinant twist of the coefficient of a compact-derivative-bounded linear form on
the position principal series of `expand es`, the two real matrix zeta integrals have entire
normalizations of strip growth by the real pair `L`-factors of `[character d]` and `expand es`,
satisfying the normalized functional equation at every point. -/
def RealMatrixPairNormalizedGrowthStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (es : List RealBlock), realRank es = n →
    ∀ (f : principalSeries ℝ n (realPositionCharacter (expand es)))
    (ℓ : principalSeries ℝ n (realPositionCharacter (expand es)) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r (expand es) ℓ →
    ∀ (d : RealCharacterData) (Φ : 𝓢(Mat, ℂ)) (b : ℝˣ),
    let F (g : G) := realDetCharacter d g * ℓ (translate r (expand es) g f)
    RealJacquet.HasRealPairNormalizedGrowth [RealBlock.character d] (expand es)
      ([RealBlock.character d].map RealLocalJacquet.dualBlock)
      ((expand es).map RealLocalJacquet.dualBlock) b (NNReal.sqrt ‖(b : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) 1
      (realMatrixZeta μ F Φ) (realMatrixZeta μ (F ∘ ιg) (matrixTransform b Φ))

theorem realMatrixPairNormalizedGrowth : RealMatrixPairNormalizedGrowthStatement (r := r) := by
  intro μ hμ κ hκ hκs es hes f ℓ hℓ d Φ b F
  obtain ⟨cs, hcs⟩ := exists_expand_eq_map_character es
  have hlen : cs.length = n := by
    rw [← realRank_map_character, ← hcs, realRank_expand, hes]
  obtain ⟨σ, M, Md, -, -, -, hM, hMd, hZM, hZdM, hpair⟩ :=
    realMatrixPairIdentity_expand μ κ es hes f ℓ hℓ d Φ b
  obtain ⟨τ, N, Nd, hN, hNd, hNg, hNdg, hR⟩ :=
    realMatrixTwistedNormalizedGrowth μ κ (expand es) f ℓ hℓ d Φ b
  have hL (s : ℂ) : (torusL
      (fun i : I => RealBlockPosition.realPositionSign (expand es) i + d.parity)
      (fun i : I => GramFormula.realPositionExponent (expand es) i + d.exponent) s)⁻¹ =
      (realPairLFactor [RealBlock.character d] (expand es)).denominator s := by
    rw [hcs, torusL_eq_pair cs hlen d s, inv_inv]
  have hLd (s : ℂ) : (torusL
      (fun i : I => RealBlockPosition.realPositionSign (expand es) i + d.parity)
      (-fun i : I => GramFormula.realPositionExponent (expand es) i + d.exponent) s)⁻¹ =
      (realPairLFactor ([RealBlock.character d].map RealLocalJacquet.dualBlock)
        ((expand es).map RealLocalJacquet.dualBlock)).denominator s := by
    rw [hcs, torusL_neg_eq_pair cs hlen d s, inv_inv]
  have hP : RealJacquet.ContinuationPackage (realMatrixZeta μ F Φ)
      (realMatrixZeta μ (F ∘ ιg) (matrixTransform b Φ))
      (fun s => ((realPairLFactor [RealBlock.character d] (expand es)).denominator s)⁻¹)
      (fun s => ((realPairLFactor ([RealBlock.character d].map RealLocalJacquet.dualBlock)
        ((expand es).map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon [RealBlock.character d] (expand es) b (NNReal.sqrt ‖(b : ℝ)‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s : ℂ)) 1 :=
    ⟨σ, M, Md, hM, hMd, hZM, hZdM, hpair⟩
  refine RealJacquet.hasRealPairNormalizedGrowth_of_continuationPackage hP hN hNd hNg hNdg
    (σ := τ) fun s hs => ?_
  obtain ⟨h1, h2⟩ := hR s hs
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · rw [← hL s]
  · rw [← hLd s]

end Langlands.GodementJacquet
