import Langlands.Global.RankinSelberg.AdelicSchwartzMellinHaar
import Langlands.Global.RankinSelberg.AdelicSchwartzProductMajorant
import Mathlib.MeasureTheory.Integral.Pi

/-! # Multivariable adelic Schwartz Mellin convergence -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace AdelicSchwartzMellin

/-- The actual idele-torus Mellin kernel of an adelic row function, with one
real exponent for each coordinate. -/
def ideleTorusMellinKernel (F : Type u) [Field F] [NumberField F] {n : ℕ}
    (Φ : RowVector F n → ℂ) (σ : Fin n → ℝ)
    (a : Fin n → Ideles F) : ℝ≥0∞ :=
  ‖Φ (fun _ j => (a j : Adeles F))‖ₑ *
    ∏ j, ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ σ j)

set_option backward.isDefEq.respectTransparency false in
/-- Tonelli's product formula for nonnegative functions of separate finite
coordinates. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {mu : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (mu i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi mu) =
      ∏ i, ∫⁻ x, f i x ∂mu i := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_one,
      Measure.pi_empty_univ]
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
          f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂(mu 0).prod (Measure.pi (fun i => mu i.succ)) := by
        rw [← (measurePreserving_piFinSuccAbove mu 0).symm.lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂mu 0) *
          ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂mu i.succ := by
        rw [lintegral_prod_mul (hf 0).aemeasurable
          (show Measurable (fun x : (i : Fin n) → E i.succ =>
            ∏ i, f i.succ (x i)) from
              Finset.measurable_prod _ fun i _ =>
                (hf i.succ).comp (measurable_pi_apply i)).aemeasurable,
          ih (fun i => f i.succ) (fun i => hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

variable (F : Type u) [Field F] [NumberField F]

local instance productSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance productSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance productIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance productIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩
local instance productIdeleLocallyCompact : LocallyCompactSpace (Ideles F) :=
  (ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance productIdeleSecondCountable : SecondCountableTopology (Ideles F) :=
  (ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

/-- The rank-one Mellin kernel is measurable for any fixed real exponent. -/
theorem measurable_idele_mellinKernel {Ψ : RowVector F 1 → ℂ}
    (hΨ : Continuous Ψ) (σ : ℝ) :
    Measurable (fun a : Ideles F =>
      ‖Ψ (fun _ _ => (a : Adeles F))‖ₑ *
        ENNReal.ofReal (((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ) ^ σ)) := by
  refine Measurable.mul (f := fun a : Ideles F =>
    ‖Ψ (fun _ _ => (a : Adeles F))‖ₑ) (g := fun a : Ideles F =>
      ENNReal.ofReal (((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ) ^ σ)) ?_ ?_
  · exact (hΨ.comp (continuous_pi fun _ =>
      continuous_pi fun _ => Units.continuous_val)).measurable.enorm
  · apply ENNReal.measurable_ofReal.comp
    exact (((NNReal.continuous_coe.comp Units.continuous_val).comp
      (IdeleAbsoluteValue.full F).continuous).rpow_const
        (fun a => Or.inl (IdeleAbsoluteValue.full_pos F a).ne')).measurable

/-- Multivariable Schwartz Mellin convergence for the product of arbitrary
idele Haar measures, with every coordinate exponent greater than three. -/
theorem lintegral_pi_idele_rpow_lt_top
    [CompactSpace (AdeleQuotient F)] {n : ℕ} (hn : 0 < n)
    (mu : Fin n → Measure (Ideles F)) [∀ j, Measure.IsHaarMeasure (mu j)]
    {Φ : RowVector F n → ℂ} (hΦ : EqualAnalytic.IsRowDominated F n Φ)
    (σ : Fin n → ℝ) (hσ : ∀ j, 3 < σ j) :
    ∫⁻ a : Fin n → Ideles F,
      ‖Φ (fun _ j => (a j : Adeles F))‖ₑ *
        ∏ j, ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ σ j)
      ∂Measure.pi mu < ⊤ := by
  obtain ⟨Ψ, hΨ, hbound⟩ := exists_product_schwartzBruhat_majorant F hn hΦ
  obtain ⟨hΨc, _, hΨdom⟩ := EqualAnalytic.schwartzBruhat_properties F 1 hΨ
  have hmajor : ∀ a : Fin n → Ideles F,
      ‖Φ (fun _ j => (a j : Adeles F))‖ₑ *
        ∏ j, ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ σ j) ≤
      ∏ j, (‖Ψ (fun _ _ => (a j : Adeles F))‖ₑ *
        ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ σ j)) := by
    intro a
    rw [Finset.prod_mul_distrib]
    apply mul_le_mul_left
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound (fun _ j => (a j : Adeles F)))
  refine (lintegral_mono hmajor).trans_lt ?_
  rw [lintegral_fin_prod_eq_prod _
    (fun j => measurable_idele_mellinKernel F hΨc (σ j))]
  exact ENNReal.prod_lt_top fun j _ =>
    lintegral_idele_rpow_lt_top F (mu j) hΨc hΨdom (hσ j)

/-- The multivariable result is independent of the Haar normalization on the
whole idele torus, including normalizations not presented as a product. -/
theorem lintegral_idele_torus_rpow_lt_top
    [CompactSpace (AdeleQuotient F)] {n : ℕ} (hn : 0 < n)
    (mu : Measure (Fin n → Ideles F)) [Measure.IsHaarMeasure mu]
    {Φ : RowVector F n → ℂ} (hΦ : EqualAnalytic.IsRowDominated F n Φ)
    (σ : Fin n → ℝ) (hσ : ∀ j, 3 < σ j) :
    ∫⁻ a : Fin n → Ideles F,
      ‖Φ (fun _ j => (a j : Adeles F))‖ₑ *
        ∏ j, ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ σ j)
      ∂mu < ⊤ := by
  have h := lintegral_pi_idele_rpow_lt_top F hn
    (fun _ : Fin n => (Measure.haar : Measure (Ideles F))) hΦ σ hσ
  exact (lintegral_continuousMulEquiv_lt_top_iff
    (ContinuousMulEquiv.refl (Fin n → Ideles F)) mu
      (Measure.pi (fun _ : Fin n => (Measure.haar : Measure (Ideles F)))) _).mpr h

/-- In particular every adelic Schwartz--Bruhat function has convergent
multivariable Mellin integral when every coordinate exponent exceeds three. -/
theorem lintegral_idele_torus_schwartzBruhat_rpow_lt_top
    [CompactSpace (AdeleQuotient F)] {n : ℕ} (hn : 0 < n)
    (mu : Measure (Fin n → Ideles F)) [Measure.IsHaarMeasure mu]
    {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n)
    (σ : Fin n → ℝ) (hσ : ∀ j, 3 < σ j) :
    ∫⁻ a : Fin n → Ideles F,
      ‖Φ (fun _ j => (a j : Adeles F))‖ₑ *
        ∏ j, ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ σ j)
      ∂mu < ⊤ :=
  lintegral_idele_torus_rpow_lt_top F hn mu
    (EqualAnalytic.schwartzBruhat_properties F n hΦ).2.2 σ hσ

/-- The named idele-torus kernel is integrable for a dominated positive-length
row function whenever every real coordinate exponent exceeds three. -/
theorem lintegral_ideleTorusMellinKernel_lt_top
    [CompactSpace (AdeleQuotient F)] {n : ℕ} (hn : 0 < n)
    (mu : Measure (Fin n → Ideles F)) [Measure.IsHaarMeasure mu]
    {Φ : RowVector F n → ℂ} (hΦ : EqualAnalytic.IsRowDominated F n Φ)
    (σ : Fin n → ℝ) (hσ : ∀ j, 3 < σ j) :
    ∫⁻ a, ideleTorusMellinKernel F Φ σ a ∂mu < ⊤ :=
  lintegral_idele_torus_rpow_lt_top F hn mu hΦ σ hσ

end AdelicSchwartzMellin

end Langlands.Global.RankinSelbergGlobal
