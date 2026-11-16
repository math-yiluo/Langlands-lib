import Langlands.Global.RankinSelberg.EqualAnalyticDualTransport

/-! # The entire pieces of the continuation

`EqualData` bundles a function `P = φ φ'` on `GL_n(𝔸)` (`n = r + 1`) that is continuous,
`GL_n(F)`-invariant, transforms by `χ` under scalars and has chamber decay in a fixed Siegel
decomposition, together with a standard character `ψ` and `Φ ∈ S(𝔸^n)`.

With `L = log |det|`, `Θ(g) = Θ(Φ, g)` and `Θ^ι(g) = Θ(Φ̂, ᵗg⁻¹)`, the amplitudes
`a₁ = 1_(L ≥ 0) P Θ` and `a₂ = 1_(L < 0) P Θ^ι` have `∫ |a_i| e^(σ L) < ∞` for every real `σ`
(`integrable_amp₁`, `integrable_amp₂`), so

`A(s) = ∫ a₁ e^(s L)` and `Ã(s) = ∫ a₂ e^(-s L)`

are entire and bounded in vertical strips. The residual integrands `1_(L<0) P e^(t L)` and
`1_(L≥0) P e^(t L)` are integrable for `Re t` large, respectively small.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance contSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance contSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local notation "E" => GeneralLinearGroupPoints.adelicEquiv
local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph

/-- The data of the equal-rank analytic theory. -/
structure EqualData (F : Type u) [Field F] [NumberField F] (r : ℕ) where
  χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ
  P : Points F (r + 1) → ℂ
  hPc : Continuous P
  hPr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
    P (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = P g
  hcent : ∀ (a : Points F 1) (g : Points F (r + 1)),
    P (zeta F (r + 1) a * g) = ideleChar F χ a * P g
  ψ : AddChar (Adeles F) ℂ
  hψ : IsStandardAdditiveCharacter F ψ
  Φ : RowVector F (r + 1) → ℂ
  hΦ : Φ ∈ schwartzBruhat F (r + 1)
  Q₁ : Set (AdelicGL F (r + 1))
  K : ℝ
  hQ₁ : IsCompact Q₁
  hdec : ∀ g : AdelicGL F (r + 1), ∃ (c : RationalGL F (r + 1)) (x : Fin (r + 1) → ℝ)
    (q : AdelicGL F (r + 1)), q ∈ Q₁ ∧ AdelicGL.rational F (r + 1) c * g = torusA (F := F) x * q ∧
      CuspidalL2.Chamber K x
  A₀ : ℝ
  hPd : PointDecay Q₁ K P A₀

namespace EqualData

variable {F : Type u} [Field F] [NumberField F] {r : ℕ} (D : EqualData F r)

/-- The measure on `GL_n(F) \ GL_n(𝔸)`. -/
abbrev μq : Measure (AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1))) :=
  AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (r + 1))

/-- `L(g) = log |det g|`. -/
def Lg (g : Points F (r + 1)) : ℝ := Real.log (detNorm F (r + 1) g)

/-- The Fourier transform `Φ̂`. -/
def Φh : RowVector F (r + 1) → ℂ := fourierTransform F (r + 1) D.ψ D.Φ

/-- `Θ(g) = Θ(Φ, g)`. -/
def Θ (g : Points F (r + 1)) : ℂ := thetaSum F (r + 1) D.Φ (E F (r + 1) g)

/-- `Θ^ι(g) = Θ(Φ̂, ᵗg⁻¹)`. -/
def Θι (g : Points F (r + 1)) : ℂ := thetaSum F (r + 1) D.Φh (E F (r + 1) (iota F (r + 1) g))

/-- The amplitude `1_(L ≥ 0) P Θ`. -/
def amp₁ (g : Points F (r + 1)) : ℂ := if 0 ≤ Lg g then D.P g * D.Θ g else 0

/-- The amplitude `1_(L < 0) P Θ^ι`. -/
def amp₂ (g : Points F (r + 1)) : ℂ := if Lg g < 0 then D.P g * D.Θι g else 0

/-- `A(s) = ∫ a₁ e^(s L)`. -/
def A (s : ℂ) : ℂ := ∫ x, D.amp₁ (Quotient.out x) * Complex.exp (s * (Lg (Quotient.out x) : ℝ)) ∂μq

/-- `Ã(s) = ∫ a₂ e^(-s L)`. -/
def At (s : ℂ) : ℂ :=
  ∫ x, D.amp₂ (Quotient.out x) * Complex.exp (s * (-Lg (Quotient.out x) : ℝ)) ∂μq

/-! ### Invariance and measurability -/

theorem Lg_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    Lg (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = Lg g := by
  rw [Lg, Lg, UnequalAnalytic.detNorm_rational_mul]

theorem measurable_Lg : Measurable (Lg (F := F) (r := r)) :=
  Real.measurable_log.comp (UnequalAnalytic.continuous_detNorm F (r + 1)).measurable

variable [CompactSpace (AdeleQuotient F)]

theorem hΦc : Continuous D.Φ := (schwartzBruhat_properties F (r + 1) D.hΦ).1

theorem hΦdom : IsRowDominated F (r + 1) D.Φ := (schwartzBruhat_properties F (r + 1) D.hΦ).2.2

theorem hΦhc : Continuous D.Φh := (fourierTransform_properties F (r + 1) D.ψ D.hψ D.hΦ).1

theorem hΦhdom : IsRowDominated F (r + 1) D.Φh :=
  (fourierTransform_properties F (r + 1) D.ψ D.hψ D.hΦ).2

theorem Θ_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.Θ (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.Θ g := by
  rw [Θ, Θ, adelicEquiv_rational_mul, thetaSum_rational_mul]

theorem Θι_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.Θι (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.Θι g := by
  unfold Θι
  rw [UnequalAnalytic.iota_mul, UnequalAnalytic.iota_rational, adelicEquiv_rational_mul,
    thetaSum_rational_mul]

theorem amp₁_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.amp₁ (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.amp₁ g := by
  simp only [amp₁, Lg_rational_mul, D.hPr, Θ_rational_mul]

theorem amp₂_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.amp₂ (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.amp₂ g := by
  simp only [amp₂, Lg_rational_mul, D.hPr, Θι_rational_mul]

theorem measurable_Θ : Measurable D.Θ :=
  (stronglyMeasurable_thetaSum F (r + 1) D.hΦc).measurable

theorem measurable_Θι : Measurable D.Θι :=
  (stronglyMeasurable_thetaSum F (r + 1) D.hΦhc).measurable.comp
    (UnequalAnalytic.continuous_iota F (r + 1)).measurable

theorem measurable_amp₁ : Measurable D.amp₁ :=
  Measurable.ite (measurableSet_le measurable_const measurable_Lg)
    (D.hPc.measurable.mul D.measurable_Θ) measurable_const

theorem measurable_amp₂ : Measurable D.amp₂ :=
  Measurable.ite (measurableSet_lt measurable_Lg measurable_const)
    (D.hPc.measurable.mul D.measurable_Θι) measurable_const

/-- A measurable invariant function, read on the quotient through representatives. -/
theorem measurable_out {Z : Type*} [MeasurableSpace Z] {f : Points F (r + 1) → Z}
    (hfm : Measurable f)
    (hf : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)),
      f (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = f g) :
    Measurable fun x : AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1)) =>
      f (Quotient.out x) := by
  obtain ⟨hf', hfun⟩ := lift_out_eq hf
  rw [hfun]
  exact measurable_from_quotient.2 hfm

theorem measurable_amp₁_out : Measurable fun x :
    AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1)) => D.amp₁ (Quotient.out x) :=
  measurable_out D.measurable_amp₁ D.amp₁_rational_mul

theorem measurable_amp₂_out : Measurable fun x :
    AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1)) => D.amp₂ (Quotient.out x) :=
  measurable_out D.measurable_amp₂ D.amp₂_rational_mul

theorem measurable_Lg_out : Measurable fun x :
    AdelicGroupPoints.RationalQuotient F (Scheme F (r + 1)) => Lg (Quotient.out x) :=
  measurable_out measurable_Lg Lg_rational_mul

/-! ### Choice of parameters -/

theorem exists_abs_log_le : ∃ ℓ₀ : ℝ, 0 ≤ ℓ₀ ∧
    ∀ q ∈ D.Q₁, |Real.log (absDet F (r + 1) q)| ≤ ℓ₀ := by
  obtain ⟨ℓ, hℓ⟩ := UnequalAnalytic.exists_abs_log_absDet_le (F := F) D.hQ₁
  exact ⟨max ℓ 0, le_max_right _ _, fun q hq => (hℓ q hq).trans (le_max_left _ _)⟩

theorem exists_nat_large (m : ℕ) (B : ℝ) : ∃ N : ℕ, m < N ∧ B ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_ge B
  exact ⟨max (m + 1) N, by omega, hN.trans (by exact_mod_cast le_max_right _ _)⟩

/-! ### Finiteness of the region integrals -/

/-- The theta factor `Θ⁺(Φ, g)`. -/
def V₁ (g : Points F (r + 1)) : ℝ≥0∞ := thetaNorm F (r + 1) D.Φ (E F (r + 1) g)

/-- The theta factor `Θ⁺(Φ̂, ᵗg⁻¹)`. -/
def V₂ (g : Points F (r + 1)) : ℝ≥0∞ :=
  thetaNorm F (r + 1) D.Φh (E F (r + 1) (iota F (r + 1) g))

theorem measurable_V₁ : Measurable D.V₁ := measurable_thetaNorm F (r + 1) D.hΦc

theorem measurable_V₂ : Measurable D.V₂ :=
  (measurable_thetaNorm F (r + 1) D.hΦhc).comp (UnequalAnalytic.continuous_iota F (r + 1)).measurable

theorem V₁_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.V₁ (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.V₁ g := by
  rw [V₁, V₁, adelicEquiv_rational_mul, thetaNorm_rational_mul]

theorem V₂_rational_mul (c : RationalGroupPoints F (Scheme F (r + 1))) (g : Points F (r + 1)) :
    D.V₂ (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * g) = D.V₂ g := by
  unfold V₂
  rw [UnequalAnalytic.iota_mul, UnequalAnalytic.iota_rational, adelicEquiv_rational_mul,
    thetaNorm_rational_mul]

theorem nat_div_bound {N : ℕ} {B : ℝ} (hN : ((r + 1 : ℕ) : ℝ) * B ≤ N) :
    B ≤ (N : ℝ) / ((r + 1 : ℕ) : ℝ) := by
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem lintegral_ge_V₁_lt_top (σ : ℝ) :
    ∫⁻ x, regionGe D.P σ D.V₁ (Quotient.out x) ∂μq < ⊤ := by
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := D.exists_abs_log_le
  obtain ⟨N, hN1, hN2⟩ := exists_nat_large ((r + 1) * Module.finrank ℚ F)
    (((r + 1 : ℕ) : ℝ) * (σ * Module.finrank ℚ F + D.A₀ + 1))
  obtain ⟨V₀, hV₀, hV⟩ := thetaNorm_chamber_le D.hΦdom D.hQ₁ N hN1
  have hb := nat_div_bound (r := r) hN2
  exact lintegral_region_ge_lt_top D.hQ₁ D.hdec hℓ₀0 hℓ₀ D.hPc D.hPr D.hPd D.measurable_V₁
    D.V₁_rational_mul (Nat.cast_nonneg N) hV₀ (fun x q hq => hV x q hq) (by linarith)

theorem lintegral_lt_V₁_lt_top {σ : ℝ}
    (hσ : 1 ≤ σ * Module.finrank ℚ F - (((r + 1) * Module.finrank ℚ F + 1 : ℕ) : ℝ) /
      ((r + 1 : ℕ) : ℝ) - D.A₀) :
    ∫⁻ x, regionLt D.P σ D.V₁ (Quotient.out x) ∂μq < ⊤ := by
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := D.exists_abs_log_le
  obtain ⟨V₀, hV₀, hV⟩ := thetaNorm_chamber_le D.hΦdom D.hQ₁ ((r + 1) * Module.finrank ℚ F + 1)
    (Nat.lt_succ_self _)
  exact lintegral_region_lt_lt_top D.hQ₁ D.hdec hℓ₀0 hℓ₀ D.hPc D.hPr D.hPd D.measurable_V₁
    D.V₁_rational_mul (Nat.cast_nonneg _) hV₀ (fun x q hq => hV x q hq) (by linarith)

theorem lintegral_ge_V₂_lt_top {σ : ℝ}
    (hσ : σ * Module.finrank ℚ F + (((r + 1) * Module.finrank ℚ F + 1 : ℕ) : ℝ) /
      ((r + 1 : ℕ) : ℝ) + D.A₀ ≤ -1) :
    ∫⁻ x, regionGe D.P σ D.V₂ (Quotient.out x) ∂μq < ⊤ := by
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := D.exists_abs_log_le
  obtain ⟨V₀, hV₀, hV⟩ := thetaNorm_iota_chamber_le D.hΦhdom D.hQ₁
    ((r + 1) * Module.finrank ℚ F + 1) (Nat.lt_succ_self _)
  exact lintegral_region_ge_lt_top D.hQ₁ D.hdec hℓ₀0 hℓ₀ D.hPc D.hPr D.hPd D.measurable_V₂
    D.V₂_rational_mul (Nat.cast_nonneg _) hV₀ (fun x q hq => hV x q hq) hσ

theorem lintegral_lt_V₂_lt_top (σ : ℝ) :
    ∫⁻ x, regionLt D.P σ D.V₂ (Quotient.out x) ∂μq < ⊤ := by
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := D.exists_abs_log_le
  obtain ⟨N, hN1, hN2⟩ := exists_nat_large ((r + 1) * Module.finrank ℚ F)
    (((r + 1 : ℕ) : ℝ) * (1 + D.A₀ - σ * Module.finrank ℚ F))
  obtain ⟨V₀, hV₀, hV⟩ := thetaNorm_iota_chamber_le D.hΦhdom D.hQ₁ N hN1
  have hb := nat_div_bound (r := r) hN2
  exact lintegral_region_lt_lt_top D.hQ₁ D.hdec hℓ₀0 hℓ₀ D.hPc D.hPr D.hPd D.measurable_V₂
    D.V₂_rational_mul (Nat.cast_nonneg N) hV₀ (fun x q hq => hV x q hq) (by linarith)

theorem one_chamber_le (x : Fin (r + 1) → ℝ) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 * Real.exp (0 * spread x) * Real.exp (0 * ∑ i, x i)) := by
  simp

theorem lintegral_ge_one_lt_top {σ : ℝ} (hσ : σ * Module.finrank ℚ F + 0 + D.A₀ ≤ -1) :
    ∫⁻ x, regionGe D.P σ (fun _ => 1) (Quotient.out x) ∂μq < ⊤ := by
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := D.exists_abs_log_le
  exact lintegral_region_ge_lt_top D.hQ₁ D.hdec hℓ₀0 hℓ₀ D.hPc D.hPr D.hPd measurable_const
    (fun _ _ => rfl) le_rfl zero_le_one (fun x _ _ => one_chamber_le x) hσ

theorem lintegral_lt_one_lt_top {σ : ℝ} (hσ : 1 ≤ σ * Module.finrank ℚ F + 0 - D.A₀) :
    ∫⁻ x, regionLt D.P σ (fun _ => 1) (Quotient.out x) ∂μq < ⊤ := by
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := D.exists_abs_log_le
  exact lintegral_region_lt_lt_top D.hQ₁ D.hdec hℓ₀0 hℓ₀ D.hPc D.hPr D.hPd measurable_const
    (fun _ _ => rfl) le_rfl zero_le_one (fun x _ _ => one_chamber_le x) hσ

/-! ### Integrability -/

theorem enorm_norm_mul_exp_le {p θ : ℂ} {v : ℝ≥0∞} (hθ : ‖θ‖ₑ ≤ v) (a : ℝ) :
    ‖‖p * θ‖ * Real.exp a‖ₑ ≤ ‖p‖ₑ * ENNReal.ofReal (Real.exp a) * v := by
  rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    enorm_mul, mul_right_comm]
  gcongr

theorem integrable_amp₁ (σ : ℝ) :
    Integrable (fun x => ‖D.amp₁ (Quotient.out x)‖ * Real.exp (σ * Lg (Quotient.out x))) μq := by
  refine ⟨((D.measurable_amp₁_out.norm).mul (Real.measurable_exp.comp
    (measurable_const.mul measurable_Lg_out))).aestronglyMeasurable,
    lt_of_le_of_lt (lintegral_mono fun x => ?_) (D.lintegral_ge_V₁_lt_top σ)⟩
  dsimp only
  generalize Quotient.out x = g
  by_cases h : 0 ≤ Real.log (detNorm F (r + 1) g)
  · have h' : 0 ≤ Lg g := h
    simp only [amp₁, h', ↓reduceIte]
    rw [regionGe, Set.indicator_of_mem (show g ∈ {g : Points F (r + 1) |
      0 ≤ Real.log (detNorm F (r + 1) g)} from h)]
    exact enorm_norm_mul_exp_le (enorm_thetaSum_le _ _ _) _
  · have h' : ¬ 0 ≤ Lg g := h
    simp only [amp₁, h', ↓reduceIte, norm_zero, zero_mul, enorm_zero, zero_le]

theorem integrable_amp₂ (σ : ℝ) :
    Integrable (fun x => ‖D.amp₂ (Quotient.out x)‖ * Real.exp (σ * -Lg (Quotient.out x))) μq := by
  refine ⟨((D.measurable_amp₂_out.norm).mul (Real.measurable_exp.comp
    (measurable_const.mul measurable_Lg_out.neg))).aestronglyMeasurable,
    lt_of_le_of_lt (lintegral_mono fun x => ?_) (D.lintegral_lt_V₂_lt_top (-σ))⟩
  dsimp only
  generalize Quotient.out x = g
  by_cases h : Real.log (detNorm F (r + 1) g) < 0
  · have h' : Lg g < 0 := h
    simp only [amp₂, h', ↓reduceIte]
    rw [regionLt, Set.indicator_of_mem (show g ∈ {g : Points F (r + 1) |
      Real.log (detNorm F (r + 1) g) < 0} from h), show σ * -Lg g = -σ * Lg g by ring]
    exact enorm_norm_mul_exp_le (enorm_thetaSum_le _ _ _) _
  · have h' : ¬ Lg g < 0 := h
    simp only [amp₂, h', ↓reduceIte, norm_zero, zero_mul, enorm_zero, zero_le]

theorem enorm_mul_cexp_eq (p t : ℂ) (L : ℝ) :
    ‖p * Complex.exp (t * (L : ℂ))‖ₑ = ‖p‖ₑ * ENNReal.ofReal (Real.exp (t.re * L)) := by
  rw [enorm_mul, ← ofReal_norm (Complex.exp _), Complex.norm_exp, Complex.re_mul_ofReal]

theorem integrable_resLt {t : ℂ} (ht : 1 ≤ t.re * Module.finrank ℚ F + 0 - D.A₀) :
    Integrable (fun x => resLt F r D.P t (Quotient.out x)) μq := by
  refine ⟨(measurable_out (measurable_resLt D.hPc t)
    (resLt_rational_mul D.hPr t)).aestronglyMeasurable,
    lt_of_le_of_lt (lintegral_mono fun x => ?_) (D.lintegral_lt_one_lt_top ht)⟩
  dsimp only
  generalize Quotient.out x = g
  by_cases h : Real.log (detNorm F (r + 1) g) < 0
  · simp only [resLt, h, ↓reduceIte]
    rw [regionLt, Set.indicator_of_mem (show g ∈ {g : Points F (r + 1) |
      Real.log (detNorm F (r + 1) g) < 0} from h), enorm_mul_cexp_eq, mul_one]
  · simp only [resLt, h, ↓reduceIte, enorm_zero, zero_le]

theorem integrable_resGe {t : ℂ} (ht : t.re * Module.finrank ℚ F + 0 + D.A₀ ≤ -1) :
    Integrable (fun x => resGe F r D.P t (Quotient.out x)) μq := by
  refine ⟨(measurable_out (measurable_resGe D.hPc t)
    (resGe_rational_mul D.hPr t)).aestronglyMeasurable,
    lt_of_le_of_lt (lintegral_mono fun x => ?_) (D.lintegral_ge_one_lt_top ht)⟩
  dsimp only
  generalize Quotient.out x = g
  by_cases h : 0 ≤ Real.log (detNorm F (r + 1) g)
  · simp only [resGe, h, ↓reduceIte]
    rw [regionGe, Set.indicator_of_mem (show g ∈ {g : Points F (r + 1) |
      0 ≤ Real.log (detNorm F (r + 1) g)} from h), enorm_mul_cexp_eq, mul_one]
  · simp only [resGe, h, ↓reduceIte, enorm_zero, zero_le]

/-! ### The entire functions -/

theorem differentiable_A : Differentiable ℂ D.A :=
  UnequalAnalytic.differentiable_integral_mul_cexp D.measurable_amp₁_out.aestronglyMeasurable
    measurable_Lg_out.aestronglyMeasurable D.integrable_amp₁

theorem differentiable_At : Differentiable ℂ D.At :=
  UnequalAnalytic.differentiable_integral_mul_cexp D.measurable_amp₂_out.aestronglyMeasurable
    measurable_Lg_out.neg.aestronglyMeasurable D.integrable_amp₂

theorem bounded_A (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖D.A s‖ ≤ C :=
  UnequalAnalytic.exists_norm_integral_mul_cexp_le D.integrable_amp₁ a b

theorem bounded_At (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖D.At s‖ ≤ C :=
  UnequalAnalytic.exists_norm_integral_mul_cexp_le D.integrable_amp₂ a b

theorem integrable_A_integrand (s : ℂ) : Integrable (fun x => D.amp₁ (Quotient.out x) *
    Complex.exp (s * (Lg (Quotient.out x) : ℝ))) μq :=
  UnequalAnalytic.integrable_mul_cexp D.measurable_amp₁_out.aestronglyMeasurable
    measurable_Lg_out.aestronglyMeasurable D.integrable_amp₁ s

theorem integrable_At_integrand (s : ℂ) : Integrable (fun x => D.amp₂ (Quotient.out x) *
    Complex.exp (s * (-Lg (Quotient.out x) : ℝ))) μq :=
  UnequalAnalytic.integrable_mul_cexp D.measurable_amp₂_out.aestronglyMeasurable
    measurable_Lg_out.neg.aestronglyMeasurable D.integrable_amp₂ s

end EqualData

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
