import Langlands.Global.RankinSelberg.WhittakerCompactTorusIntegral
import Langlands.Global.RankinSelberg.AdelicGaugeCompactTranslate
import Mathlib.MeasureTheory.Group.LIntegral

/-! # A single torus criterion for right standard compact invariant kernels -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.WhittakerStandardCompactTorusIntegral

open AdelicDiagonalUnipotentModulus WhittakerCompactTorusIntegral

local instance standardTorusSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance : MeasurableSpace (Ideles F) := borel _
local instance : BorelSpace (Ideles F) := ⟨rfl⟩

theorem continuous_diagonalModulus_coe :
    Continuous fun d : Fin n → Ideles F => (diagonalModulus F n d : ℝ≥0) := by
  simp only [diagonalModulus_coe]
  apply continuous_finsetProd
  intro p _
  exact Units.continuous_val.comp ((IdeleAbsoluteValue.full F).continuous.comp
    ((continuous_apply p.1).mul (continuous_apply p.2.1).inv))

/-- A diagonal right translate multiplies the inverse-modulus weighted
torus integral by the modulus of the translating diagonal. -/
theorem lintegral_diagonal_translate
    (mu : Measure (Fin n → Ideles F)) [mu.IsHaarMeasure]
    (f : Points F n → ℝ≥0∞) (e : Fin n → Ideles F) :
    (∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
      f (gaugeDiagonalPoint F n (d * e)) ∂mu) =
      ((diagonalModulus F n e : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          f (gaugeDiagonalPoint F n d) ∂mu := by
  have hw (d : Fin n → Ideles F) :
      (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) =
        ((diagonalModulus F n e : ℝ≥0) : ℝ≥0∞) *
          (((diagonalModulus F n (d * e) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    congr 1
    simp only [map_mul, Units.val_mul, mul_inv]
    simp [mul_comm, Units.ne_zero]
  calc
    _ = ∫⁻ d, ((diagonalModulus F n e : ℝ≥0) : ℝ≥0∞) *
        ((((diagonalModulus F n (d * e) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          f (gaugeDiagonalPoint F n (d * e))) ∂mu := by
      apply lintegral_congr
      intro d
      rw [hw, mul_assoc]
    _ = ((diagonalModulus F n e : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ d, (((diagonalModulus F n (d * e) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          f (gaugeDiagonalPoint F n (d * e)) ∂mu :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = _ := by
      rw [lintegral_mul_right_eq_self
        (fun d => (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          f (gaugeDiagonalPoint F n d)) e]

/-- Right invariance under the actual standard adelic compact subgroup. -/
def IsRightStandardCompactInvariant (f : Points F n → ℝ≥0∞) : Prop :=
  ∀ (k : gaugeStandardCompact F n) (g : Points F n),
    f (g * (k : Points F n)) = f g

theorem diagonal_mul_iwasawa
    (f : Points F n → ℝ≥0∞)
    (hfN : ∀ (v : unipotentAdelic F n) (g : Points F n),
      f ((v : Points F n) * g) = f g)
    (hfK : IsRightStandardCompactInvariant F n f)
    (d e : Fin n → Ideles F) (u : unipotentAdelic F n)
    (k : gaugeStandardCompact F n) :
    f (gaugeDiagonalPoint F n d *
      ((u : Points F n) * gaugeDiagonalPoint F n e * (k : Points F n))) =
      f (gaugeDiagonalPoint F n (d * e)) := by
  let v : unipotentAdelic F n :=
    ⟨_, gaugeDiagonalPoint_conj_mem_unipotent F n d u⟩
  have heq : gaugeDiagonalPoint F n d *
      ((u : Points F n) * gaugeDiagonalPoint F n e * (k : Points F n)) =
      (v : Points F n) *
        (gaugeDiagonalPoint F n (d * e) * (k : Points F n)) := by
    rw [gaugeDiagonalPoint_mul]
    dsimp only [v]
    group
  rw [heq, hfN, hfK]

/-- For a left unipotent invariant, right standard compact invariant kernel,
one finite weighted torus integral supplies bounds on every compact family
of right translates. -/
theorem compactTorusBound_of_single
    (mu : Measure (Fin n → Ideles F)) [mu.IsHaarMeasure]
    (f : Points F n → ℝ≥0∞)
    (hfN : ∀ (v : unipotentAdelic F n) (g : Points F n),
      f ((v : Points F n) * g) = f g)
    (hfK : IsRightStandardCompactInvariant F n f)
    (hfinite : ∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
      f (gaugeDiagonalPoint F n d) ∂mu < ⊤)
    (C : Set (Points F n)) (hC : IsCompact C) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ C,
      ∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        f (gaugeDiagonalPoint F n d * c) ∂mu ≤ B := by
  obtain ⟨D, hD, hfac⟩ := exists_compact_gaugeDiagonal_parameters F n hC
  obtain ⟨B, hB⟩ := hD.bddAbove_image (continuous_diagonalModulus_coe F n).continuousOn
  let I := ∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
    f (gaugeDiagonalPoint F n d) ∂mu
  refine ⟨(B : ℝ≥0∞) * I, ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite, ?_⟩
  intro c hc
  obtain ⟨e, he, u, k, rfl⟩ := hfac c hc
  simp_rw [diagonal_mul_iwasawa F n f hfN hfK]
  rw [lintegral_diagonal_translate]
  exact mul_le_mul (ENNReal.coe_le_coe.mpr (hB (mem_image_of_mem _ he)))
    le_rfl bot_le bot_le

/-- A single finite inverse-modulus weighted torus integral implies finiteness
on the actual Whittaker quotient for measurable kernels with the two
standard invariances. -/
theorem lintegral_whittakerQuotient_lt_top_of_single
    [CompactSpace (AdeleQuotient F)]
    (mu : Measure (Fin n → Ideles F)) [mu.IsHaarMeasure]
    (f : Points F n → ℝ≥0∞) (hfm : Measurable f)
    (hfN : ∀ (v : unipotentAdelic F n) (g : Points F n),
      f ((v : Points F n) * g) = f g)
    (hfK : IsRightStandardCompactInvariant F n f)
    (hfinite : ∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
      f (gaugeDiagonalPoint F n d) ∂mu < ⊤) :
    ∫⁻ q : WhittakerQuotient F n, f q.out ∂whittakerQuotientMeasure F n < ⊤ :=
  lintegral_whittakerQuotient_lt_top_of_compactTorusBound F n mu f hfm hfN
    (compactTorusBound_of_single F n mu f hfN hfK hfinite)

end Langlands.Global.RankinSelbergGlobal.WhittakerStandardCompactTorusIntegral
