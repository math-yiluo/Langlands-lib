import Langlands.Analysis.FiniteProductLpStatement

/-!
# Finite-product preservation and reflection of `MemLp`

The proof uses Tonelli's theorem for nonnegative extended-real power integrals.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace Langlands

universe uι uX

private theorem aemeasurable_separated_prod
    {ι : Type uι} [Fintype ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {g : ∀ i, X i → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) (μ i)) :
    AEMeasurable (fun x : ∀ i, X i => ∏ i, g i (x i)) (Measure.pi μ) := by
  exact Finset.aemeasurable_fun_prod _ fun i _ =>
    (hg i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)

set_option backward.isDefEq.respectTransparency false in
private theorem lintegral_fin_separated_prod
    {n : ℕ} {X : Fin n → Type uX} [∀ i, MeasurableSpace (X i)]
    {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {g : ∀ i, X i → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) (μ i)) :
    (∫⁻ x : ∀ i, X i, ∏ i, g i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ t, g i t ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : X 0 × ((i : Fin n) → X i.succ),
            g 0 x.1 * ∏ i : Fin n, g i.succ (x.2 i)
            ∂(μ 0).prod (Measure.pi (fun i => μ i.succ)) := by
          rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ t, g 0 t ∂μ 0) * ∏ i : Fin n, ∫⁻ t, g i.succ t ∂μ i.succ := by
          rw [lintegral_prod_mul (hg 0)
            (aemeasurable_separated_prod (fun i : Fin n => hg i.succ)),
            ih (fun i => hg i.succ)]
        _ = _ := by rw [Fin.prod_univ_succ]

private theorem lintegral_separated_prod
    {ι : Type uι} [Fintype ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {g : ∀ i, X i → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) (μ i)) :
    (∫⁻ x : ∀ i, X i, ∏ i, g i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ t, g i t ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_separated_prod (fun i => hg (e i))

private theorem aestronglyMeasurable_separated_prod
    {ι : Type uι} [Fintype ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {f : ∀ i, X i → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) :
    AEStronglyMeasurable (fun x : ∀ i, X i => ∏ i, f i (x i)) (Measure.pi μ) := by
  exact Finset.aestronglyMeasurable_fun_prod _ fun i _ =>
    (hf i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)

private theorem lintegral_power_separated_prod
    {ι : Type uι} [Fintype ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {f : ∀ i, X i → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) (r : ℝ) :
    (∫⁻ x : ∀ i, X i, ‖∏ i, f i (x i)‖ₑ ^ r ∂Measure.pi μ) =
      ∏ i, ∫⁻ t, ‖f i t‖ₑ ^ r ∂μ i := by
  simp_rw [enorm_eq_nnnorm, nnnorm_prod, ← ENNReal.prod_coe_rpow]
  exact lintegral_separated_prod (fun i => (hf i).enorm.pow_const r)

private theorem memLp_ofReal_iff_power_integral
    {Y : Type uX} [MeasurableSpace Y] {ν : Measure Y} {h : Y → ℝ}
    (hh : AEStronglyMeasurable h ν) {r : ℝ} (hr : 0 < r) :
    MemLp h (ENNReal.ofReal r) ν ↔ (∫⁻ t, ‖h t‖ₑ ^ r ∂ν) < ∞ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top hh,
    ENNReal.toReal_ofReal hr.le]

private theorem power_integral_ne_zero
    {Y : Type uX} [MeasurableSpace Y] {ν : Measure Y} {h : Y → ℝ}
    (hh : AEStronglyMeasurable h ν) (hn : ¬ (h =ᵐ[ν] (0 : Y → ℝ)))
    {r : ℝ} (hr : 0 < r) : (∫⁻ t, ‖h t‖ₑ ^ r ∂ν) ≠ 0 := by
  intro hz
  apply hn
  have hae := (lintegral_eq_zero_iff' (hh.enorm.pow_const r)).mp hz
  filter_upwards [hae] with t ht
  simpa only [Pi.zero_apply, ENNReal.rpow_eq_zero_iff_of_pos hr, enorm_eq_zero] using ht

/-- Separated finite products preserve membership in every positive finite `L^r`. -/
theorem finiteProductMemLpPreservation : FiniteProductMemLpPreservationStatement.{uι, uX} := by
  intro ι _ _ X _ μ _ f r hr hf
  have hfm : ∀ i, AEStronglyMeasurable (f i) (μ i) :=
    fun i => (hf i).aestronglyMeasurable
  apply (memLp_ofReal_iff_power_integral (aestronglyMeasurable_separated_prod hfm) hr).mpr
  rw [lintegral_power_separated_prod hfm]
  exact ENNReal.prod_lt_top (fun i _ => (memLp_ofReal_iff_power_integral (hfm i) hr).mp (hf i))

/-- If no factor is a.e. zero, finite-product `L^r` membership reflects to every factor. -/
theorem finiteProductMemLpNonzeroIff : FiniteProductMemLpNonzeroIffStatement.{uι, uX} := by
  classical
  intro ι _ _ X _ μ _ f hf hn r hr
  constructor
  · intro hprod i
    apply (memLp_ofReal_iff_power_integral (hf i) hr).mpr
    have hfinite : (∏ j, ∫⁻ t, ‖f j t‖ₑ ^ r ∂μ j) < ∞ := by
      rw [← lintegral_power_separated_prod hf]
      exact (memLp_ofReal_iff_power_integral (aestronglyMeasurable_separated_prod hf) hr).mp hprod
    apply lt_top_iff_ne_top.mpr
    intro hi
    exact hfinite.ne (WithTop.prod_eq_top (Finset.mem_univ i) hi
      (fun j _ => power_integral_ne_zero (hf j) (hn j) hr))
  · exact finiteProductMemLpPreservation ι X μ f r hr

/-- Preservation and nonzero-factor reflection for dependent finite products in `MemLp`. -/
theorem finiteProductMemLp : FiniteProductMemLpStatement.{uι, uX} :=
  ⟨finiteProductMemLpPreservation, finiteProductMemLpNonzeroIff⟩

end Langlands
