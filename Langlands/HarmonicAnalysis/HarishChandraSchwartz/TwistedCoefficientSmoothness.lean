import Langlands.HarmonicAnalysis.TorusFourierSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Completeness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedPairing
import Langlands.Representation.Plancherel.SmoothTensorFamilies

/-! # Smoothness of twisted coefficients (core of Waldspurger's Proposition VII.1.3)

For `f ∈ C(G)`, a continuous `φ` with `ν_{-r}(φ) < ∞` and a measurable `n : G → (J → ℤ)` with
`‖n(g)‖ ≤ C (1 + σ(g))`, the function
`z ↦ ∫_G f(g) φ(g) ∏ⱼ zⱼ^{n(g)ⱼ} dμ(g)` on the torus `J → Circle` is smooth, depends linearly on
`f`, and each iterated angle derivative `∂_l` of it is bounded by
`|C|^{|l|} ν_{d+r+|l|}(f) ν_{-r}(φ) c`, where `d` and `c` are the exponent and the constant of
Lemma II.1.5 in `L2Weights`. This is Waldspurger's estimate (2) in the proof of
Proposition VII.1.3 and its consequences, in torus coordinates.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Filter
open Langlands.HarmonicAnalysis.TorusFourier

namespace Langlands.HarishChandraSchwartz

universe u

section Weight

variable {G : Type u} {Ξ σ : G → ℝ}

/-- Multiplying by `(1 + σ)^k` shifts the index of the seminorm by `k`:
`ν_s((1 + σ)^k f) = ν_{s+k}(f)`. -/
theorem nu_one_add_pow_smul (hσ : ∀ g, 0 ≤ σ g) (s : ℝ) (k : ℕ) (f : G → ℂ) :
    nu Ξ σ s (fun g => (1 + σ g) ^ k • f g) = nu Ξ σ (s + k) f := by
  unfold nu
  refine iSup_congr fun g => ?_
  have hb : 0 < 1 + σ g := by linarith [hσ g]
  have key : (1 + σ g) ^ k * ((Ξ g)⁻¹ * (1 + σ g) ^ s) =
      (Ξ g)⁻¹ * (1 + σ g) ^ (s + k) := by
    rw [Real.rpow_add hb, Real.rpow_natCast]
    ring
  rw [weight, weight, ← key, ENNReal.ofReal_mul (pow_nonneg hb.le k), enorm_smul,
    Real.enorm_of_nonneg (pow_nonneg hb.le k)]
  ring

end Weight

section Moments

variable {G : Type u} [MeasurableSpace G] {μ : Measure G} {Ξ σ : G → ℝ}
  {J : Type*} [Fintype J] {n : G → J → ℤ} {C : ℝ}

namespace L2Weights

/-- Waldspurger's estimate (2) in the proof of Proposition VII.1.3, in lattice coordinates:
if `‖n(g)‖ ≤ C (1 + σ(g))`, then
`∫_G ‖n(g)‖^k |f(g)| |φ(g)| dμ ≤ |C|^k ν_{d+r+k}(f) ν_{-r}(φ) c`. -/
theorem lintegral_enorm_pow_mul_le (hw : L2Weights μ Ξ σ)
    (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (r : ℝ) (k : ℕ) {f φ : G → ℂ}
    (hf : nu Ξ σ (hw.exponent + r + k) f ≠ ⊤) (hφ : nu Ξ σ (-r) φ ≠ ⊤) :
    ∫⁻ g, ‖n g‖ₑ ^ k * (‖f g‖ₑ * ‖φ g‖ₑ) ∂μ ≤
      ‖C‖ₑ ^ k * (nu Ξ σ (hw.exponent + r + k) f * nu Ξ σ (-r) φ * hw.const) := by
  have hfk : nu Ξ σ (hw.exponent + r) (fun g => (1 + σ g) ^ k • f g) ≠ ⊤ := by
    rwa [nu_one_add_pow_smul hw.nonneg]
  calc ∫⁻ g, ‖n g‖ₑ ^ k * (‖f g‖ₑ * ‖φ g‖ₑ) ∂μ
      ≤ ∫⁻ g, ‖C‖ₑ ^ k * (‖(1 + σ g) ^ k • f g‖ₑ * ‖φ g‖ₑ) ∂μ := by
        refine lintegral_mono fun g => ?_
        have hng : ‖n g‖ₑ ≤ ‖C‖ₑ * ‖1 + σ g‖ₑ := by
          rw [← enorm_mul]
          exact enorm_le_iff_norm_le.mpr ((hnσ g).trans (Real.le_norm_self _))
        calc ‖n g‖ₑ ^ k * (‖f g‖ₑ * ‖φ g‖ₑ)
            ≤ (‖C‖ₑ * ‖1 + σ g‖ₑ) ^ k * (‖f g‖ₑ * ‖φ g‖ₑ) := by gcongr
          _ = ‖C‖ₑ ^ k * (‖(1 + σ g) ^ k • f g‖ₑ * ‖φ g‖ₑ) := by
            rw [enorm_smul, enorm_pow, mul_pow]
            ring
    _ = ‖C‖ₑ ^ k * ∫⁻ g, ‖(1 + σ g) ^ k • f g‖ₑ * ‖φ g‖ₑ ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)
    _ ≤ _ := by
        gcongr
        have h := hw.lintegral_enorm_mul_le_of_nu r hfk hφ
        rwa [nu_one_add_pow_smul hw.nonneg] at h

variable [TopologicalSpace G] [OpensMeasurableSpace G]

/-- For `f` and `φ` continuous with all `ν_s(f)` finite and `ν_{-r}(φ)` finite, the product
`f φ` has finite moments `∫ ‖n‖^k |f φ| dμ` of all orders. -/
theorem hasTorusMoments_mul (hw : L2Weights μ Ξ σ) (hn : Measurable n)
    (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) {f φ : G → ℂ} (hfc : Continuous f)
    (hf : ∀ s, nu Ξ σ s f ≠ ⊤) (hφc : Continuous φ) {r : ℝ} (hφ : nu Ξ σ (-r) φ ≠ ⊤) :
    HasTorusMoments μ n (fun g => f g * φ g) := by
  have hnm : Measurable fun g => ‖n g‖ :=
    (measurable_of_countable fun m : J → ℤ => ‖m‖).comp hn
  refine ⟨(hfc.mul hφc).aestronglyMeasurable, fun k => ⟨?_, ?_⟩⟩
  · exact (hnm.pow_const k).aestronglyMeasurable.mul (hfc.mul hφc).aestronglyMeasurable.norm
  · simp only [HasFiniteIntegral, enorm_mul, enorm_pow, enorm_norm]
    refine lt_of_le_of_lt (hw.lintegral_enorm_pow_mul_le hnσ r k (hf _) hφ) ?_
    exact ENNReal.mul_lt_top (ENNReal.pow_ne_top enorm_ne_top).lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (hf _).lt_top hφ.lt_top) hw.const_lt_top)

/-- The real form of estimate (2): `∫_G ‖n(g)‖^k |f(g) φ(g)| dμ ≤ |C|^k ν_{d+r+k}(f) ν_{-r}(φ) c`. -/
theorem integral_norm_pow_mul_le (hw : L2Weights μ Ξ σ) (hn : Measurable n)
    (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) {f φ : G → ℂ} (hfc : Continuous f)
    (hf : ∀ s, nu Ξ σ s f ≠ ⊤) (hφc : Continuous φ) {r : ℝ} (hφ : nu Ξ σ (-r) φ ≠ ⊤)
    (k : ℕ) :
    ∫ g, ‖n g‖ ^ k * ‖f g * φ g‖ ∂μ ≤
      ‖C‖ ^ k * (nu Ξ σ (hw.exponent + r + k) f * nu Ξ σ (-r) φ * hw.const).toReal := by
  have hmom := hw.hasTorusMoments_mul hn hnσ hfc hf hφc hφ
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun g => by positivity)
    (hmom.2 k).1]
  have hfin : ‖C‖ₑ ^ k * (nu Ξ σ (hw.exponent + r + k) f * nu Ξ σ (-r) φ * hw.const) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hf _) hφ) hw.const_lt_top.ne)
  calc (∫⁻ g, ENNReal.ofReal (‖n g‖ ^ k * ‖f g * φ g‖) ∂μ).toReal
      = (∫⁻ g, ‖n g‖ₑ ^ k * (‖f g‖ₑ * ‖φ g‖ₑ) ∂μ).toReal := by
        congr 1
        refine lintegral_congr fun g => ?_
        rw [← Real.enorm_of_nonneg (by positivity)]
        simp only [enorm_mul, enorm_pow, enorm_norm]
    _ ≤ (‖C‖ₑ ^ k * (nu Ξ σ (hw.exponent + r + k) f * nu Ξ σ (-r) φ * hw.const)).toReal :=
        ENNReal.toReal_mono hfin (hw.lintegral_enorm_pow_mul_le hnσ r k (hf _) hφ)
    _ = ‖C‖ ^ k * (nu Ξ σ (hw.exponent + r + k) f * nu Ξ σ (-r) φ * hw.const).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm]

end L2Weights

end Moments

section Family

variable {G : Type u} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G]
  [Group G] [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} {Ξ σ : G → ℝ} {J : Type*} [Fintype J] {n : G → J → ℤ} {C : ℝ}
  {φ : G → ℂ} {r : ℝ}

namespace Space

theorem hasTorusMoments_mul (hw : L2Weights μ Ξ σ) (hn : Measurable n)
    (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ) (hφ : nu Ξ σ (-r) φ ≠ ⊤)
    (f : Space Ξ σ) : HasTorusMoments μ n (fun g => f g * φ g) :=
  hw.hasTorusMoments_mul hn hnσ (Space.continuous f) (Space.nu_ne_top f) hφc hφ

end Space

/-- The twisted coefficients of `C(G)` against `φ`, in torus coordinates: `f ∈ C(G)` goes to
the smooth function `z ↦ ∫_G f(g) φ(g) ∏ⱼ zⱼ^{n(g)ⱼ} dμ(g)` on `J → Circle`. For `φ` the
coefficient `g ↦ ⟨ω(g) v, v̌⟩` and `f` replaced by `f̌`, this is Waldspurger's
`χ ↦ ⟨(ω ⊗ χ)(f̌) v, v̌⟩` of Proposition VII.1.3 when `χ(g) = ∏ⱼ zⱼ^{n(g)ⱼ}`. -/
def twistedCoefficientFamily (hw : L2Weights μ Ξ σ) (hn : Measurable n)
    (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ) (hφ : nu Ξ σ (-r) φ ≠ ⊤) :
    Space Ξ σ →ₗ[ℂ] Plancherel.smoothFiniteTorusFunctions J where
  toFun f := ⟨torusSynthesis μ n (fun g => f g * φ g),
    isSmoothFiniteTorusFunction_torusSynthesis hn (Space.hasTorusMoments_mul hw hn hnσ hφc hφ f)⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    change torusSynthesis μ n (fun g => (f₁ g + f₂ g) * φ g) =
      torusSynthesis μ n (fun g => f₁ g * φ g) + torusSynthesis μ n (fun g => f₂ g * φ g)
    rw [← torusSynthesis_add hn (Space.hasTorusMoments_mul hw hn hnσ hφc hφ f₁)
      (Space.hasTorusMoments_mul hw hn hnσ hφc hφ f₂)]
    simp only [add_mul]
  map_smul' c f := by
    apply Subtype.ext
    change torusSynthesis μ n (fun g => (c * f g) * φ g) =
      c • torusSynthesis μ n (fun g => f g * φ g)
    rw [← torusSynthesis_const_mul]
    simp only [mul_assoc]

theorem twistedCoefficientFamily_apply (hw : L2Weights μ Ξ σ) (hn : Measurable n)
    (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ) (hφ : nu Ξ σ (-r) φ ≠ ⊤)
    (f : Space Ξ σ) (z : J → Circle) :
    (twistedCoefficientFamily hw hn hnσ hφc hφ f : (J → Circle) → ℂ) z =
      ∫ g, f g * φ g * torusCharacter (n g) z ∂μ :=
  rfl

variable [DecidableEq J]

/-- The iterated angle derivatives of a twisted coefficient are the twisted coefficients of
`f φ` multiplied by `∏_{j ∈ l} i n(g)ⱼ`. -/
theorem torusPartialDerivList_twistedCoefficientFamily (hw : L2Weights μ Ξ σ)
    (hn : Measurable n) (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) (l : List J) (z : J → Circle) :
    torusPartialDerivList l (twistedCoefficientFamily hw hn hnσ hφc hφ f) z =
      ∫ g, (l.map fun j => Complex.I * (n g j : ℂ)).prod * (f g * φ g) *
        torusCharacter (n g) z ∂μ := by
  change torusPartialDerivList l (torusSynthesis μ n (fun g => f g * φ g)) z = _
  rw [torusPartialDerivList_torusSynthesis hn (Space.hasTorusMoments_mul hw hn hnσ hφc hφ f)]
  rfl

/-- Waldspurger's estimate (2) for the derivative `∂_l`, uniformly on the torus:
`|∂_l Φ_f(z)| ≤ |C|^{|l|} ν_{d+r+|l|}(f) ν_{-r}(φ) c`. -/
theorem norm_torusPartialDerivList_twistedCoefficientFamily_le (hw : L2Weights μ Ξ σ)
    (hn : Measurable n) (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) (l : List J) (z : J → Circle) :
    ‖torusPartialDerivList l (twistedCoefficientFamily hw hn hnσ hφc hφ f) z‖ ≤
      ‖C‖ ^ l.length *
        (nu Ξ σ (hw.exponent + r + l.length) f * nu Ξ σ (-r) φ * hw.const).toReal := by
  change ‖torusPartialDerivList l (torusSynthesis μ n (fun g => f g * φ g)) z‖ ≤ _
  exact (norm_torusPartialDerivList_torusSynthesis_le hn
    (Space.hasTorusMoments_mul hw hn hnσ hφc hφ f) l z).trans
      (hw.integral_norm_pow_mul_le hn hnσ (Space.continuous f) (Space.nu_ne_top f) hφc hφ _)

/-- Continuity of `f ↦ Φ_f` (the second assertion of Proposition VII.1.3) in seminorm form: for
every list `l` of directions there are an index `s` and a constant `c'` with
`sup_z |∂_l Φ_f(z)| ≤ c' ν_s(f)` for all `f ∈ C(G)`. -/
theorem exists_norm_torusPartialDerivList_twistedCoefficientFamily_le (hw : L2Weights μ Ξ σ)
    (hn : Measurable n) (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)) (hφc : Continuous φ)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (l : List J) :
    ∃ s c' : ℝ, ∀ (f : Space Ξ σ) (z : J → Circle),
      ‖torusPartialDerivList l (twistedCoefficientFamily hw hn hnσ hφc hφ f) z‖ ≤
        c' * (nu Ξ σ s f).toReal := by
  refine ⟨hw.exponent + r + l.length, ‖C‖ ^ l.length * (nu Ξ σ (-r) φ * hw.const).toReal,
    fun f z => ?_⟩
  refine (norm_torusPartialDerivList_twistedCoefficientFamily_le hw hn hnσ hφc hφ f l z).trans_eq ?_
  rw [mul_assoc, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

end Family

end Langlands.HarishChandraSchwartz
