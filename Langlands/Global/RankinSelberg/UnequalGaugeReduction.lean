import Langlands.Global.RankinSelberg.UnequalUnfoldingGaugeStatement
import Langlands.Global.RankinSelberg.CuspCentralBound

/-! # Reduction of the unequal-rank gauge premises to Whittaker gauge integrals

The premises `WhittakerGaugeIntegrable` and `DualWhittakerGaugeIntegrable` of the unequal-rank
unfolding involve a Whittaker function of the large group and a cusp form of the small group.
This module removes the cusp form: it is bounded by a fixed power of `|det|`
(`CuspCentralBound`), and the remaining Whittaker majorant is left invariant under `N_m(𝔸)`, so
its integral over `N_m(F) \ GL_m(𝔸)` is its integral over `N_m(𝔸) \ GL_m(𝔸)`. What remains are
two statements about Whittaker functions alone: `UnequalPadGaugeStatement` and
`UnequalRectGaugeStatement`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance gaugeReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance gaugeReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance gaugeReductionRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

section Premises

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Gauge integrability of the padded Whittaker function: there is `C ≥ 0` such that for every
standard additive character `ψ`, every vector `v` and every real `σ > C`, the integral of
`|W_φ(diag(h, I_{n-m}))| |det h|^σ` over `N_m(𝔸) \ GL_m(𝔸)` (at quotient representatives, for
`whittakerQuotientMeasure`) is finite. -/
def PadWhittakerGaugeBound {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (σ : ℝ), C < σ →
      ∫⁻ p : WhittakerQuotient F (t + 1),
          ‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) p.out)‖ₑ *
            ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
        ∂whittakerQuotientMeasure F (t + 1) < ⊤

/-- Gauge integrability of the dual Whittaker function along the rectangular unipotent
directions: there is `C ≥ 0` such that for every standard `ψ`, every `v` and every real
`σ > C`, the iterated integral of `|W̃(rect(h, x) w')| |det h|^σ`, over `x` in
`M_{(n-m-1)×m}(𝔸)` for `rectangleMeasure` and then over `h ∈ N_m(𝔸) \ GL_m(𝔸)`, is finite.
Here `W̃ = dualFunction W_φ` and `w' = unfoldingWeyl F h`. -/
def RectWhittakerGaugeBound {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (σ : ℝ), C < σ →
      ∫⁻ p : WhittakerQuotient F (t + 1),
          (∫⁻ x, ‖translateFunction F (r + 1) (unfoldingWeyl F h)
              (dualFunction F (r + 1) (cuspWhittaker F T ψ v)) (rectangularPoint F h p.out x)‖ₑ
            ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
            ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
        ∂whittakerQuotientMeasure F (t + 1) < ⊤

end Premises

/-- `PadWhittakerGaugeBound` for every actual unequal-rank cuspidal realization. -/
def UnequalPadGaugeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r) (T : Automorphic.CuspidalOperatorRealization F r),
    PadWhittakerGaugeBound F h T

/-- `RectWhittakerGaugeBound` for every actual unequal-rank cuspidal realization. -/
def UnequalRectGaugeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r) (T : Automorphic.CuspidalOperatorRealization F r),
    RectWhittakerGaugeBound F h T

/-- The conditional reduction: the two Whittaker gauge statements imply the gauge premises
`UnequalUnfoldingGaugeStatement` of the unequal-rank unfolding. -/
def UnequalGaugeReductionStatement : Prop :=
  UnequalPadGaugeStatement.{u} → UnequalRectGaugeStatement.{u} →
    UnequalUnfoldingGaugeStatement.{u}

namespace GaugeReduction

variable (F : Type u) [Field F] [NumberField F]

/-- The norm of the determinant power is a real power of the determinant norm. -/
theorem norm_detPower_eq_rpow {n : ℕ} (g : Points F n) (z : ℂ) :
    ‖detPower F n g z‖ = detNorm F n g ^ z.re := by
  rw [UnequalAnalytic.norm_detPower, Real.rpow_def_of_pos (detNorm_pos F n g), mul_comm]

theorem re_unfolding_exponent (s : ℂ) (k : ℕ) :
    (s - (k : ℂ) / 2).re = s.re - (k : ℝ) / 2 := by
  simp

/-- The determinant norm is left invariant under `N_m(𝔸)`. -/
theorem detNorm_unipotent_mul (n : ℕ) (u : unipotentAdelic F n) (x : Points F n) :
    detNorm F n ((u : Points F n) * x) = detNorm F n x := by
  rw [detNorm_mul, detNorm_unipotent, one_mul]

/-- A measurable left `N_m(𝔸)`-invariant majorant has the same lower integral over
`N_m(F) \ GL_m(𝔸)` as over `N_m(𝔸) \ GL_m(𝔸)` with `whittakerQuotientMeasure`. -/
theorem lintegral_rationalQuotient_eq {t : ℕ} {M : Points F (t + 1) → ℝ≥0∞}
    (hM : Measurable M)
    (hMN : ∀ (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)),
      M ((n : Points F (t + 1)) * x) = M x) :
    ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)), M q.out
        ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
          (isDiscrete_unipotentRationalImage F (t + 1)) =
      ∫⁻ p : WhittakerQuotient F (t + 1), M p.out ∂whittakerQuotientMeasure F (t + 1) := by
  have hMq : Measurable (fun p : WhittakerQuotient F (t + 1) => M p.out) := by
    rw [out_eq_lift (unipotentAdelic F (t + 1)) _ hMN]
    exact measurable_from_quotient.mpr hM
  rw [whittakerQuotientMeasure, lintegral_map hMq (measurable_toWhittakerQuotient F (t + 1))]
  congr 1
  funext q'
  have h1 : toWhittakerQuotient F (t + 1) q' =
      LeftCosetSpace.mk (unipotentAdelic F (t + 1)) q'.out := by
    conv_lhs => rw [← Quotient.out_eq q']
    rfl
  rw [h1]
  obtain ⟨n, hn⟩ := exists_out_mk_eq (unipotentAdelic F (t + 1)) q'.out
  rw [hn]
  exact (hMN n _).symm

variable [CompactSpace (AdeleQuotient F)]

/-- The padded Whittaker function has `N_m(𝔸)`-invariant absolute value. -/
theorem norm_cuspWhittaker_pad_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (n : unipotentAdelic F (t + 1))
    (x : Points F (t + 1)) :
    ‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
        ((n : Points F (t + 1)) * x))‖ =
      ‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x)‖ := by
  rw [pad_mul]
  have hp : pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) (n : Points F (t + 1)) =
      (padUnipotent F (Nat.le_of_lt (Nat.succ_lt_succ h)) n : Points F (r + 1)) := rfl
  rw [hp, cuspWhittaker_mul_left F T ψ hψ v, norm_mul, norm_genericCharacter F r ψ hψ.2.2.2,
    one_mul]

/-- **Premise G from the padded Whittaker gauge bound.** -/
theorem whittakerGaugeIntegrable_of_pad {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (hpad : PadWhittakerGaugeBound F h T) :
    WhittakerGaugeIntegrable F h T T' := by
  obtain ⟨C₁, -, hW⟩ := hpad
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_cuspFunction_le F T'
  refine ⟨max 0 (C₁ + ((r - t : ℕ) : ℝ) / 2 - β), le_max_left _ _,
    fun ψ hψ v v' s hs => ?_⟩
  obtain ⟨C', hC'0, hC'⟩ := hβ v'
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = s.re - ((r - t : ℕ) : ℝ) / 2 + β := ⟨_, rfl⟩
  have hσ : C₁ < σ := by
    rw [hσdef]
    linarith [le_max_right 0 (C₁ + ((r - t : ℕ) : ℝ) / 2 - β)]
  have hfin := hW ψ hψ v σ hσ
  have hfm : Measurable (ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s) :=
    measurable_ordinaryKernel F h (measurable_cuspWhittaker F T ψ hψ v)
      (continuous_cuspFunction F T' v').measurable s
  have hfΓ : ∀ (k : unipotentRationalImage F (t + 1)) (x : Points F (t + 1)),
      ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s
          ((k : Points F (t + 1)) * x) =
        ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s x :=
    fun k x => ordinaryKernel_rational_mul F h T T' ψ hψ v v' s k.property x
  let M : Points F (t + 1) → ℝ≥0∞ := fun g =>
    ‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ₑ *
      ENNReal.ofReal (detNorm F (t + 1) g ^ σ)
  have hM : Measurable M :=
    ((measurable_cuspWhittaker F T ψ hψ v).comp (continuous_pad F _).measurable).enorm.mul
      ((continuous_detNorm F (t + 1)).measurable.pow_const σ).ennreal_ofReal
  have hMN : ∀ (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)),
      M ((n : Points F (t + 1)) * x) = M x := by
    intro n x
    simp only [M]
    rw [← ofReal_norm, ← ofReal_norm, norm_cuspWhittaker_pad_unipotent_mul F h T ψ hψ v n x,
      detNorm_unipotent_mul]
  have hbound : ∀ g : Points F (t + 1),
      ‖ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s g‖ₑ ≤
        ENNReal.ofReal C' * M g := by
    intro g
    have hd := detNorm_pos F (t + 1) g
    have hreal : ‖ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s g‖ ≤
        C' * (‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ *
          detNorm F (t + 1) g ^ σ) := by
      unfold ordinaryKernel
      rw [norm_mul, norm_mul, norm_detPower_eq_rpow, re_unfolding_exponent]
      calc ‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ *
            ‖cuspFunction F T' v' g‖ * detNorm F (t + 1) g ^ (s.re - ((r - t : ℕ) : ℝ) / 2)
          ≤ ‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ *
            (C' * detNorm F (t + 1) g ^ β) *
              detNorm F (t + 1) g ^ (s.re - ((r - t : ℕ) : ℝ) / 2) := by
            gcongr
            exact hC' g
        _ = C' * (‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ *
            detNorm F (t + 1) g ^ σ) := by
            rw [hσdef, Real.rpow_add hd]
            ring
    calc ‖ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s g‖ₑ
        = ENNReal.ofReal
            ‖ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s g‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (C' *
            (‖cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ *
              detNorm F (t + 1) g ^ σ)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C' * M g := by
          simp only [M]
          rw [ENNReal.ofReal_mul hC'0, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  show Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (t + 1)) =>
      ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s q.out) _
  refine ⟨?_, ?_⟩
  · have hm : Measurable (LeftCosetSpace.lift (unipotentRationalImage F (t + 1)) _ hfΓ) :=
      measurable_from_quotient.mpr hfm
    rw [out_eq_lift _ _ hfΓ]
    exact hm.aestronglyMeasurable
  · calc ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)),
          ‖ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s q.out‖ₑ
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
            (isDiscrete_unipotentRationalImage F (t + 1))
        ≤ ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)),
            ENNReal.ofReal C' * M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
            (isDiscrete_unipotentRationalImage F (t + 1)) :=
          lintegral_mono fun q => hbound q.out
      _ = ENNReal.ofReal C' * ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)),
            M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
            (isDiscrete_unipotentRationalImage F (t + 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C' *
            ∫⁻ p : WhittakerQuotient F (t + 1), M p.out ∂whittakerQuotientMeasure F (t + 1) := by
          rw [lintegral_rationalQuotient_eq F hM hMN]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The real rectangular integral of a norm is at most the lower integral of the norm. -/
theorem ofReal_integral_norm_le_lintegral {α : Type*} [MeasurableSpace α] (mu : Measure α)
    (f : α → ℂ) :
    ENNReal.ofReal (∫ x, ‖f x‖ ∂mu) ≤ ∫⁻ x, ‖f x‖ₑ ∂mu := by
  calc ENNReal.ofReal (∫ x, ‖f x‖ ∂mu)
      = ‖∫ x, ‖f x‖ ∂mu‖ₑ := by
        rw [← ofReal_norm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    _ ≤ ∫⁻ x, ‖‖f x‖‖ₑ ∂mu := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x, ‖f x‖ₑ ∂mu := by simp_rw [enorm_norm]

/-- **Premise G' from the rectangular Whittaker gauge bound.** -/
theorem dualWhittakerGaugeIntegrable_of_rect {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (hrect : RectWhittakerGaugeBound F h T) :
    DualWhittakerGaugeIntegrable F h T T' := by
  obtain ⟨C₂, -, hW⟩ := hrect
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_dualCuspFunction_le F T'
  refine ⟨max 0 (C₂ + ((r - t : ℕ) : ℝ) / 2 - β), le_max_left _ _,
    fun ψ hψ v v' s hs => ?_⟩
  obtain ⟨C', hC'0, hC'⟩ := hβ v'
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = s.re - ((r - t : ℕ) : ℝ) / 2 + β := ⟨_, rfl⟩
  have hσ : C₂ < σ := by
    rw [hσdef]
    linarith [le_max_right 0 (C₂ + ((r - t : ℕ) : ℝ) / 2 - β)]
  have hfin := hW ψ hψ v σ hσ
  let I : Points F (t + 1) → ℝ := fun g =>
    ∫ x, ‖dualWhittaker F h T ψ v (rectangularPoint F h g x)‖
      ∂rectangleMeasure F (r - (t + 1)) (t + 1)
  have hIm : Measurable I :=
    measurable_dualRectNormIntegral F h (measurable_dualWhittaker F h T ψ hψ v)
  have hIN : ∀ (n : unipotentAdelic F (t + 1)) (g : Points F (t + 1)),
      I ((n : Points F (t + 1)) * g) = I g :=
    fun n g => dualRectNormIntegral_unipotent_mul F h T ψ hψ v n g
  have hI0 : ∀ g, 0 ≤ I g := fun g => integral_nonneg fun x => norm_nonneg _
  let f : Points F (t + 1) → ℝ := fun g =>
    I g * ‖dualFunction F (t + 1) (cuspFunction F T' v') g‖ *
      ‖detPower F (t + 1) g (s - ((r - t : ℕ) : ℂ) / 2)‖
  have hfm : Measurable f :=
    (hIm.mul (continuous_dualCuspFunction F T' v').measurable.norm).mul
      (continuous_detPower F (t + 1) _).measurable.norm
  have hfΓ : ∀ (k : unipotentRationalImage F (t + 1)) (x : Points F (t + 1)),
      f ((k : Points F (t + 1)) * x) = f x := by
    intro k x
    have hkN := ((mem_unipotentRationalImage_iff_mem_inf F (t + 1) k).1 k.property).2
    have hkR := unipotentRationalImage_le F (t + 1) k.property
    simp only [f]
    rw [hIN ⟨k, hkN⟩ x, dualCuspFunction_rational_mul F T' v' hkR x,
      detPower_rational_mul F (t + 1) hkR x]
  let M : Points F (t + 1) → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (I g) * ENNReal.ofReal (detNorm F (t + 1) g ^ σ)
  have hM : Measurable M :=
    hIm.ennreal_ofReal.mul ((continuous_detNorm F (t + 1)).measurable.pow_const σ).ennreal_ofReal
  have hMN : ∀ (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)),
      M ((n : Points F (t + 1)) * x) = M x := by
    intro n x
    simp only [M]
    rw [hIN n x, detNorm_unipotent_mul]
  have hbound : ∀ g : Points F (t + 1), ‖f g‖ₑ ≤ ENNReal.ofReal C' * M g := by
    intro g
    have hd := detNorm_pos F (t + 1) g
    have hreal : ‖f g‖ ≤ C' * (I g * detNorm F (t + 1) g ^ σ) := by
      simp only [f]
      rw [norm_mul, norm_mul, norm_norm, norm_norm, Real.norm_of_nonneg (hI0 g),
        norm_detPower_eq_rpow, re_unfolding_exponent]
      calc I g * ‖dualFunction F (t + 1) (cuspFunction F T' v') g‖ *
            detNorm F (t + 1) g ^ (s.re - ((r - t : ℕ) : ℝ) / 2)
          ≤ I g * (C' * detNorm F (t + 1) g ^ β) *
              detNorm F (t + 1) g ^ (s.re - ((r - t : ℕ) : ℝ) / 2) := by
            gcongr
            exact hC' g
        _ = C' * (I g * detNorm F (t + 1) g ^ σ) := by
            rw [hσdef, Real.rpow_add hd]
            ring
    calc ‖f g‖ₑ = ENNReal.ofReal ‖f g‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (C' * (I g * detNorm F (t + 1) g ^ σ)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C' * M g := by
          simp only [M]
          rw [ENNReal.ofReal_mul hC'0, ENNReal.ofReal_mul (hI0 g)]
  have hMW : ∀ g : Points F (t + 1), M g ≤
      (∫⁻ x, ‖translateFunction F (r + 1) (unfoldingWeyl F h)
          (dualFunction F (r + 1) (cuspWhittaker F T ψ v)) (rectangularPoint F h g x)‖ₑ
        ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
        ENNReal.ofReal (detNorm F (t + 1) g ^ σ) := by
    intro g
    simp only [M]
    gcongr
    exact ofReal_integral_norm_le_lintegral _ _
  show Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (t + 1)) => f q.out) _
  refine ⟨?_, ?_⟩
  · have hm : Measurable (LeftCosetSpace.lift (unipotentRationalImage F (t + 1)) _ hfΓ) :=
      measurable_from_quotient.mpr hfm
    rw [out_eq_lift _ _ hfΓ]
    exact hm.aestronglyMeasurable
  · calc ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)), ‖f q.out‖ₑ
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
            (isDiscrete_unipotentRationalImage F (t + 1))
        ≤ ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)),
            ENNReal.ofReal C' * M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
            (isDiscrete_unipotentRationalImage F (t + 1)) :=
          lintegral_mono fun q => hbound q.out
      _ = ENNReal.ofReal C' * ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (t + 1)),
            M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
            (isDiscrete_unipotentRationalImage F (t + 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C' *
            ∫⁻ p : WhittakerQuotient F (t + 1), M p.out ∂whittakerQuotientMeasure F (t + 1) := by
          rw [lintegral_rationalQuotient_eq F hM hMN]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hfin)
          exact lintegral_mono fun p => hMW p.out

end GaugeReduction

open GaugeReduction in
/-- Proof of the conditional reduction `UnequalGaugeReductionStatement`. -/
theorem unequalGaugeReduction : UnequalGaugeReductionStatement.{u} := by
  intro hP hR
  exact ⟨fun F _ _ _ r t h T T' => whittakerGaugeIntegrable_of_pad F h T T' (hP F r t h T),
    fun F _ _ _ r t h T T' => dualWhittakerGaugeIntegrable_of_rect F h T T' (hR F r t h T)⟩

end Langlands.Global.RankinSelbergGlobal
