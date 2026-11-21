import Langlands.Global.RankinSelberg.RealLocalEqualJointIntegrability
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Analysis.LandauMellin
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # Interval bounds and holomorphy of the real unfolded equal-rank integral -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData charData_character_apply)
open Langlands.LandauMellin (eqOn_halfPlane isOpen_halfPlane)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (n + 1) ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "U" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "pad" => (padGL (R := ℝ) (Nat.le_succ (t + 1)))
local notation "P" => (ArchimedeanLocal.detPower (K := ℝ) realNormalizedAbs)

/-! ### Continuous weights from Schwartz seminorms -/

private theorem continuous_seminormSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) :
    Continuous (fun Ψ : 𝓢(E, ℂ) => ∑ r ∈ Finset.Iic (k, 0), SchwartzMap.seminorm ℝ r.1 r.2 Ψ) :=
  continuous_finsetSum _ fun r _ => (schwartz_withSeminorms ℝ E ℂ).continuous_seminorm r

private theorem seminormSup_le_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (Ψ : 𝓢(E, ℂ)) :
    (Finset.Iic (k, 0)).sup (fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2) Ψ ≤
      ∑ r ∈ Finset.Iic (k, 0), SchwartzMap.seminorm ℝ r.1 r.2 Ψ :=
  Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
    fun _ hi => Finset.single_le_sum (f := fun r : ℕ × ℕ => SchwartzMap.seminorm ℝ r.1 r.2 Ψ)
      (fun _ _ => apply_nonneg _ _) hi

/-! ### Monotonicity of the kernel in the separated exponent -/

/-- On an interval of real parts of the separated exponent, the size of the unfolded
kernel is bounded by the sum of its sizes at the two endpoints. -/
theorem norm_equalUnfoldedKernel_le_endpoints (d₁ d₂ d : RealCharacterData)
    (h₁ : d₁.exponent.re ≤ d.exponent.re) (h₂ : d.exponent.re ≤ d₂.exponent.re)
    (Ψ : Y → ℂ) (W : G → ℂ) (V : H → ℂ) (s : ℂ) (p : Q × H) :
    ‖equalUnfoldedKernel d Ψ W V s p‖ ≤
      ‖equalUnfoldedKernel d₁ Ψ W V s p‖ + ‖equalUnfoldedKernel d₂ Ψ W V s p‖ := by
  have hpos : 0 < |p.2.val.det| := abs_pos.mpr (determinant p.2).ne_zero
  rcases le_total 1 |p.2.val.det| with hg | hg
  · have hc : |p.2.val.det| ^ (d.exponent.re + (s + (m : ℂ) / 2).re) ≤
        |p.2.val.det| ^ (d₂.exponent.re + (s + (m : ℂ) / 2).re) :=
      Real.rpow_le_rpow_of_exponent_le hg (by linarith)
    refine le_trans ?_ (le_add_of_nonneg_left (norm_nonneg _))
    simp only [equalUnfoldedKernel, norm_mul, norm_determinantWeight_real]
    gcongr
  · have hc : |p.2.val.det| ^ (d.exponent.re + (s + (m : ℂ) / 2).re) ≤
        |p.2.val.det| ^ (d₁.exponent.re + (s + (m : ℂ) / 2).re) :=
      Real.rpow_le_rpow_of_exponent_ge hpos hg (by linarith)
    refine le_trans ?_ (le_add_of_nonneg_right (norm_nonneg _))
    simp only [equalUnfoldedKernel, norm_mul, norm_determinantWeight_real]
    gcongr

/-! ### Interval bounds -/

variable (t) in
/-- On every compact interval of the separated exponent above a threshold and every
vertical line to the right of a second threshold, the unfolded kernel is integrable for
every square Schwartz test, with absolute integral bounded by one continuous function
of the test vanishing at zero. -/
def RealLocalEqualChamberTraceStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (W : G → ℂ)
    (V : H → ℂ), Continuous W → Continuous V → RealEqualConvergence.HasGauge W →
    RealEqualConvergence.HasGauge V → (∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) →
    ∃ ρ σ : ℝ, ∀ x₁ x₂ y : ℝ, ρ ≤ x₁ → σ < y →
      ∃ weight : 𝓢(Y, ℂ) → ℝ, Continuous weight ∧ weight 0 = 0 ∧
        ∀ (Ψ : 𝓢(Y, ℂ)) (d : RealCharacterData) (s : ℂ),
          x₁ ≤ d.exponent.re → d.exponent.re ≤ x₂ → s.re = y →
          Integrable (equalUnfoldedKernel d Ψ W V s) (D.measure.prod D'.groupHaar) ∧
          ∫ p, ‖equalUnfoldedKernel d Ψ W V s p‖ ∂(D.measure.prod D'.groupHaar) ≤ weight Ψ

theorem realLocalEqualChamberTrace : RealLocalEqualChamberTraceStatement t := by
  intro D D' W V hWc hVc hWg hVg hVu
  obtain ⟨ρ, σ, h⟩ := realLocalEqualJointIntegrability D D' W V hWc hVc hWg hVg hVu
  refine ⟨ρ, σ, fun x₁ x₂ y hx hy => ?_⟩
  let x₂' := max x₁ x₂
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := h x₁ y hx hy
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := h x₂' y (hx.trans (le_max_left _ _)) hy
  let S (k : ℕ) (Ψ : 𝓢(Y, ℂ)) := ∑ r ∈ Finset.Iic (k, 0), SchwartzMap.seminorm ℝ r.1 r.2 Ψ
  have hS0 (k : ℕ) : S k 0 = 0 := by simp [S]
  refine ⟨fun Ψ => C₁ * S k₁ Ψ + C₂ * S k₂ Ψ,
    ((continuous_seminormSum k₁).const_mul _).add ((continuous_seminormSum k₂).const_mul _),
    by simp only [hS0, mul_zero, add_zero], fun Ψ d s hd₁ hd₂ hs => ?_⟩
  let e₁ := charData 0 (x₁ : ℂ)
  let e₂ := charData 0 (x₂' : ℂ)
  have he₁ : e₁.exponent.re = x₁ := Complex.ofReal_re x₁
  have he₂ : e₂.exponent.re = x₂' := Complex.ofReal_re x₂'
  obtain ⟨hi₁, hb₁⟩ := h₁ Ψ e₁ s he₁ hs
  obtain ⟨hi₂, hb₂⟩ := h₂ Ψ e₂ s he₂ hs
  have hle (p : Q × H) := norm_equalUnfoldedKernel_le_endpoints e₁ e₂ d (he₁ ▸ hd₁)
    (he₂ ▸ hd₂.trans (le_max_right _ _)) Ψ W V s p
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.groupHaar_isHaar
  have hcont := continuous_equalUnfoldedKernel d Ψ hWc hVc s
  have hI : Integrable (equalUnfoldedKernel d Ψ W V s) (D.measure.prod D'.groupHaar) :=
    (hi₁.norm.add hi₂.norm).mono' hcont.aestronglyMeasurable (.of_forall hle)
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ p, (‖equalUnfoldedKernel e₁ Ψ W V s p‖ + ‖equalUnfoldedKernel e₂ Ψ W V s p‖)
        ∂(D.measure.prod D'.groupHaar) :=
      integral_mono hI.norm (hi₁.norm.add hi₂.norm) hle
    _ = (∫ p, ‖equalUnfoldedKernel e₁ Ψ W V s p‖ ∂(D.measure.prod D'.groupHaar)) +
        ∫ p, ‖equalUnfoldedKernel e₂ Ψ W V s p‖ ∂(D.measure.prod D'.groupHaar) :=
      integral_add hi₁.norm hi₂.norm
    _ ≤ C₁ * S k₁ Ψ + C₂ * S k₂ Ψ := by
      gcongr
      · exact hb₁.trans (mul_le_mul_of_nonneg_left (seminormSup_le_sum k₁ Ψ) hC₁)
      · exact hb₂.trans (mul_le_mul_of_nonneg_left (seminormSup_le_sum k₂ Ψ) hC₂)

/-! ### Holomorphy along affine lines -/

private theorem continuous_quotientRepresentative' : Continuous (quotientRepresentative t) := by
  have h : quotientRepresentative t =
      (unipotentQuotientHomeomorph t) ∘ (fun q : Q => (1, q)) := by
    funext q
    change _ = (1 : G) * quotientRepresentative t q
    exact (one_mul _).symm
  rw [h]
  exact (unipotentQuotientHomeomorph t).continuous.comp (continuous_const.prodMk continuous_id)

private theorem ofReal_abs_cpow {x : ℝ} (hx : x ≠ 0) (z : ℂ) :
    ((|x| : ℝ) : ℂ) ^ z = Complex.exp (z * (Real.log |x| : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)),
    ← Complex.ofReal_log (abs_nonneg _), mul_comm]

/-- The unfolded kernel at a real character with prescribed parity and exponent, with all
determinant powers written as one complex exponential. -/
theorem equalUnfoldedKernel_charData (p : Fin 2) (u : ℂ) (Ψ : Y → ℂ) (W : G → ℂ) (V : H → ℂ)
    (s : ℂ) (q : Q × H) :
    equalUnfoldedKernel (charData p u) Ψ W V s q =
      Ψ q.2.val * V (pad (quotientRepresentative t q.1) * q.2) *
        (((q.2.val.det / |q.2.val.det| : ℝ) : ℂ) ^ p.val) * W (quotientRepresentative t q.1) *
        Complex.exp ((u + s + (m : ℂ) / 2) * (Real.log |q.2.val.det| : ℂ) +
          (s - 1 / 2) * (Real.log |(quotientRepresentative t q.1).val.det| : ℂ)) := by
  have hg : q.2.val.det ≠ 0 := (determinant q.2).ne_zero
  change Ψ q.2.val * V (pad (quotientRepresentative t q.1) * q.2) *
      ((charData p u).character (determinant q.2) *
        ((|(determinant q.2 : ℝ)| : ℝ) : ℂ) ^ (s + (m : ℂ) / 2)) *
      W (quotientRepresentative t q.1) *
      Complex.exp ((s - 1 / 2) *
        (Real.log |(quotientRepresentative t q.1).val.det| : ℂ)) = _
  rw [charData_character_apply]
  unfold Langlands.Archimedean.RealJacquetFrobenius.charFun
  change Ψ q.2.val * V (pad (quotientRepresentative t q.1) * q.2) *
      ((((q.2.val.det / |q.2.val.det| : ℝ) : ℂ) ^ p.val * ((|q.2.val.det| : ℝ) : ℂ) ^ u) *
        ((|q.2.val.det| : ℝ) : ℂ) ^ (s + (m : ℂ) / 2)) *
      W (quotientRepresentative t q.1) *
      Complex.exp ((s - 1 / 2) *
        (Real.log |(quotientRepresentative t q.1).val.det| : ℂ)) = _
  rw [ofReal_abs_cpow hg, ofReal_abs_cpow hg]
  rw [show (u + s + (m : ℂ) / 2) * (Real.log |q.2.val.det| : ℂ) +
      (s - 1 / 2) * (Real.log |(quotientRepresentative t q.1).val.det| : ℂ) =
      u * (Real.log |q.2.val.det| : ℂ) + (s + (m : ℂ) / 2) * (Real.log |q.2.val.det| : ℂ) +
      (s - 1 / 2) * (Real.log |(quotientRepresentative t q.1).val.det| : ℂ) by ring,
    Complex.exp_add, Complex.exp_add]
  ring

/-- On an open set of absolute convergence, the unfolded integral is holomorphic along
every real-slope affine line in the separated exponent and the spectral variable. -/
theorem differentiableOn_integral_equalUnfoldedKernel_affine (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) (p : Fin 2) (Ψ : Y → ℂ) (W : G → ℂ) (V : H → ℂ)
    (u₀ s₀ : ℂ) (c₁ c₂ : ℝ) {S : Set ℂ} (hS : IsOpen S)
    (hInt : ∀ w ∈ S,
      Integrable (equalUnfoldedKernel (charData p (u₀ + (c₁ : ℂ) * w)) Ψ W V (s₀ + (c₂ : ℂ) * w))
        (D.measure.prod D'.groupHaar)) :
    DifferentiableOn ℂ (fun w => ∫ q, equalUnfoldedKernel (charData p (u₀ + (c₁ : ℂ) * w)) Ψ W V
      (s₀ + (c₂ : ℂ) * w) q ∂(D.measure.prod D'.groupHaar)) S := by
  let A := equalUnfoldedKernel (charData p u₀) Ψ W V s₀
  let L (q : Q × H) : ℝ := (c₁ + c₂) * Real.log |q.2.val.det| +
    c₂ * Real.log |(quotientRepresentative t q.1).val.det|
  have hL : Measurable L := by
    have h₁ : Measurable fun q : Q × H => Real.log |q.2.val.det| :=
      ((Units.continuous_val.matrix_det.abs).measurable.comp measurable_snd).log
    have h₂ : Measurable fun q : Q × H => Real.log |(quotientRepresentative t q.1).val.det| :=
      ((Units.continuous_val.matrix_det.abs.comp continuous_quotientRepresentative').measurable.comp
        measurable_fst).log
    exact (h₁.const_mul _).add (h₂.const_mul _)
  have hEq (w : ℂ) (q : Q × H) :
      equalUnfoldedKernel (charData p (u₀ + (c₁ : ℂ) * w)) Ψ W V (s₀ + (c₂ : ℂ) * w) q =
        A q * Complex.exp (w * (L q : ℂ)) := by
    dsimp only [A, L]
    rw [equalUnfoldedKernel_charData, equalUnfoldedKernel_charData,
      mul_assoc _ (Complex.exp _), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hIt (w : ℂ) (hw : w ∈ S) :
      Integrable (fun q => A q * Complex.exp (w * (L q : ℂ))) (D.measure.prod D'.groupHaar) :=
    (hInt w hw).congr (.of_forall (hEq w))
  refine (differentiableOn_integral_mul_cexp hL hS hIt).congr ?_
  intro w _
  exact integral_congr_ae (.of_forall (hEq w))

/-- A deep trace identity for jointly entire functions extends to the whole product of
right half-planes on which the unfolded kernel is absolutely integrable. -/
theorem eq_mul_integral_equalUnfoldedKernel_of_deep (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) (p : Fin 2) (Ψ : Y → ℂ) (W : G → ℂ) (V : H → ℂ)
    {F N : ℂ × ℂ → ℂ} (hF : Differentiable ℂ F) (hN : Differentiable ℂ N) {τ σ : ℝ}
    (hInt : ∀ z s : ℂ, τ < z.re → σ < s.re →
      Integrable (equalUnfoldedKernel (charData p z) Ψ W V s) (D.measure.prod D'.groupHaar))
    (hDeep : ∃ τ' σ' : ℝ, ∀ z s : ℂ, τ' < z.re → σ' < s.re →
      F (z, s) = N (z, s) *
        ∫ q, equalUnfoldedKernel (charData p z) Ψ W V s q ∂(D.measure.prod D'.groupHaar)) :
    ∀ z s : ℂ, τ < z.re → σ < s.re →
      F (z, s) = N (z, s) *
        ∫ q, equalUnfoldedKernel (charData p z) Ψ W V s q ∂(D.measure.prod D'.groupHaar) := by
  obtain ⟨τ', σ', hDeep⟩ := hDeep
  let I (z s : ℂ) := ∫ q, equalUnfoldedKernel (charData p z) Ψ W V s q ∂(D.measure.prod D'.groupHaar)
  have hzI (s : ℂ) (hs : σ < s.re) :
      DifferentiableOn ℂ (fun z => I z s) {z : ℂ | τ < z.re} := by
    simpa only [I, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, zero_add,
      add_zero] using
      differentiableOn_integral_equalUnfoldedKernel_affine D D' p Ψ W V 0 s 1 0
        (isOpen_halfPlane τ) (fun z hz => by
          simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, zero_add,
            add_zero] using hInt z s hz hs)
  have hsI (z : ℂ) (hz : τ < z.re) :
      DifferentiableOn ℂ (fun s => I z s) {s : ℂ | σ < s.re} := by
    simpa only [I, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, zero_add,
      add_zero] using
      differentiableOn_integral_equalUnfoldedKernel_affine D D' p Ψ W V z 0 0 1
        (isOpen_halfPlane σ) (fun s hs => by
          simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, zero_add,
            add_zero] using hInt z s hz hs)
  have hZ (s : ℂ) (hs : max σ σ' < s.re) :
      Set.EqOn (fun z => F (z, s)) (fun z => N (z, s) * I z s) {z : ℂ | τ < z.re} :=
    eqOn_halfPlane (hF.comp (differentiable_id.prodMk (differentiable_const s))).differentiableOn
      ((hN.comp (differentiable_id.prodMk (differentiable_const s))).differentiableOn.mul
        (hzI s ((le_max_left _ _).trans_lt hs)))
      (fun z hz => hDeep z s hz ((le_max_right _ _).trans_lt hs))
  intro z s hz hs
  exact eqOn_halfPlane (hF.comp ((differentiable_const z).prodMk differentiable_id)).differentiableOn
    ((hN.comp ((differentiable_const z).prodMk differentiable_id)).differentiableOn.mul (hsI z hz))
    (fun w hw => hZ w hw hz) hs

/-! ### Normalized traces -/

private theorem norm_le_all_strip_of_stripGrowth {F : ℂ → ℂ} (hF : Continuous F)
    (h : HasStripExponentialGrowth F) (l u : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖F z‖ ≤ C * Real.exp (K * |z.im|) := by
  obtain ⟨C, K, T, hC, hK, h⟩ := h l u
  let A := max T 0
  have hRect := (isCompact_Icc (a := l) (b := u)).reProdIm (isCompact_Icc (a := -A) (b := A))
  obtain ⟨M, hM⟩ := hRect.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C M, K, hC.trans (le_max_left _ _), hK, fun z hz₁ hz₂ => ?_⟩
  by_cases ht : T ≤ |z.im|
  · exact (h z hz₁ hz₂ ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have him : |z.im| ≤ A := (lt_of_not_ge ht).le.trans (le_max_left _ _)
    have hb := hM z (Complex.mem_reProdIm.mpr ⟨⟨hz₁, hz₂⟩, abs_le.mp him⟩)
    calc
      ‖F z‖ ≤ max C M := hb.trans (le_max_right _ _)
      _ ≤ max C M * Real.exp (K * |z.im|) :=
        le_mul_of_one_le_right (hC.trans (le_max_left _ _)) (Real.one_le_exp (by positivity))

/-- The unfolded integral at the real character of parity `p` and exponent `z`,
multiplied by a constant and by two normalizing functions of `s` and `s + z`. -/
def equalNormalizedTrace (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1))
    (p : Fin 2) (A B : ℂ → ℂ) (c : ℂ) (W : G → ℂ) (V : H → ℂ) (Ψ : 𝓢(Y, ℂ)) (z s : ℂ) : ℂ :=
  c * (A s * B (s + z) *
    ∫ q, equalUnfoldedKernel (charData p z) Ψ W V s q ∂(D.measure.prod D'.groupHaar))

private theorem equalUnfoldedKernel_sub (d : RealCharacterData) (Ψ₁ Ψ₂ : 𝓢(Y, ℂ))
    (W : G → ℂ) (V : H → ℂ) (s : ℂ) :
    equalUnfoldedKernel d (Ψ₁ - Ψ₂ : 𝓢(Y, ℂ)) W V s =
      equalUnfoldedKernel d Ψ₁ W V s - equalUnfoldedKernel d Ψ₂ W V s := by
  funext q
  simp only [equalUnfoldedKernel, Pi.sub_apply, _root_.sub_apply]
  ring

/-- On a vertical line to the right of a threshold and an interval of exponents to the
right of a second threshold, differences of normalized traces are bounded by a continuous
function of the difference of the tests, vanishing at zero, times an exponential in both
imaginary parts. -/
theorem exists_equalNormalizedTrace_bound (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) {W : G → ℂ} {V : H → ℂ}
    (hWc : Continuous W) (hVc : Continuous V)
    (hWg : RealEqualConvergence.HasGauge W) (hVg : RealEqualConvergence.HasGauge V)
    (hVu : ∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖) (p : Fin 2) {A B : ℂ → ℂ}
    (hA : Continuous A) (hAg : HasStripExponentialGrowth A)
    (hB : Continuous B) (hBg : HasStripExponentialGrowth B) (c : ℂ) :
    ∃ τ σ : ℝ, ∀ l u y : ℝ, τ ≤ l → σ < y →
      ∃ (K L : ℝ) (w : 𝓢(Y, ℂ) → ℝ), 0 ≤ K ∧ 0 ≤ L ∧ Continuous w ∧ w 0 = 0 ∧
        ∀ (Ψ₁ Ψ₂ : 𝓢(Y, ℂ)) (z s : ℂ), l ≤ z.re → z.re ≤ u → s.re = y →
          ‖equalNormalizedTrace D D' p A B c W V Ψ₁ z s -
            equalNormalizedTrace D D' p A B c W V Ψ₂ z s‖ ≤
            w (Ψ₁ - Ψ₂) * Real.exp (K * |s.im| + L * |z.im|) := by
  obtain ⟨ρ, σ, h⟩ := realLocalEqualChamberTrace D D' W V hWc hVc hWg hVg hVu
  refine ⟨ρ, σ, fun l u y hl hy => ?_⟩
  obtain ⟨w₀, hw₀, hw₀0, hP⟩ := h l u y hl hy
  obtain ⟨C, K, hC, hK, hF₁⟩ := norm_le_all_strip_of_stripGrowth hA hAg y y
  obtain ⟨E, L, hE, hL, hF₂⟩ := norm_le_all_strip_of_stripGrowth hB hBg (y + l) (y + u)
  let M := ‖c‖ * (C * E)
  refine ⟨K + L, L, fun Ψ => M * w₀ Ψ, add_nonneg hK hL, hL, hw₀.const_mul _,
    by simp only [hw₀0, mul_zero], fun Ψ₁ Ψ₂ z s hz₁ hz₂ hs => ?_⟩
  have hre : (charData p z).exponent.re = z.re := rfl
  have hRaw (Ψ : 𝓢(Y, ℂ)) := hP Ψ (charData p z) s (hre ▸ hz₁) (hre ▸ hz₂) hs
  have hsub : (∫ q, equalUnfoldedKernel (charData p z) Ψ₁ W V s q ∂(D.measure.prod D'.groupHaar)) -
      ∫ q, equalUnfoldedKernel (charData p z) Ψ₂ W V s q ∂(D.measure.prod D'.groupHaar) =
      ∫ q, equalUnfoldedKernel (charData p z) (Ψ₁ - Ψ₂ : 𝓢(Y, ℂ)) W V s q
        ∂(D.measure.prod D'.groupHaar) := by
    rw [equalUnfoldedKernel_sub, ← integral_sub (hRaw Ψ₁).1 (hRaw Ψ₂).1]
    rfl
  have hF₂s := hF₂ (s + z) (by rw [Complex.add_re, hs]; gcongr) (by rw [Complex.add_re, hs]; gcongr)
  have hsum : |(s + z).im| ≤ |s.im| + |z.im| := by
    rw [Complex.add_im]
    exact abs_add_le _ _
  have hI : ‖∫ q, equalUnfoldedKernel (charData p z) (Ψ₁ - Ψ₂ : 𝓢(Y, ℂ)) W V s q
      ∂(D.measure.prod D'.groupHaar)‖ ≤ w₀ (Ψ₁ - Ψ₂) :=
    (norm_integral_le_integral_norm _).trans (hRaw (Ψ₁ - Ψ₂)).2
  dsimp only [equalNormalizedTrace]
  rw [← mul_sub, ← mul_sub, hsub]
  simp only [norm_mul]
  calc
    _ ≤ ‖c‖ * ((C * Real.exp (K * |s.im|)) *
        (E * Real.exp (L * (|s.im| + |z.im|))) * w₀ (Ψ₁ - Ψ₂)) := by
      have hb₂ := hF₂s.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hL)) hE)
      gcongr
      exact hF₁ s hs.ge hs.le
    _ = _ := by
      dsimp only [M]
      rw [add_mul, mul_add L, Real.exp_add, Real.exp_add, Real.exp_add]
      ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
