import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalField.Uniformizer

/-!
# Integrability from geometric bounds on an exhaustion by boxes

A measurable function `f` is integrable as soon as there are measurable sets `box e`
with `μ(box e) ≤ M Q^e` and, for every point `x`, some `e` with `x ∈ box e` and
`|f x| ≤ C s^e`, where `s Q < 1`: then `|f| ≤ ∑_e C s^e 1_(box e)`, whose integral
is a convergent geometric series. On a rectangular matrix space over a p-adic field the
boxes `{x : ϖ^e x_(ab) ∈ O}` have measure `(q^e μ(O))^(jl)` by the scalar Haar scaling.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockConvergence

open MeasureTheory
open scoped ENNReal NNReal

universe u uF

section Abstract

variable {X : Type u} [MeasurableSpace X]

/-- **Integrability from box bounds.** -/
theorem integrable_of_forall_exists_mem_box {μ : Measure X} {f : X → ℂ}
    (hf : AEStronglyMeasurable f μ) (box : ℕ → Set X) (hbox : ∀ e, MeasurableSet (box e))
    {M Q : ℝ≥0∞} (hM : M ≠ ∞) (hμ : ∀ e, μ (box e) ≤ M * Q ^ e) {C s : ℝ} (hC : 0 ≤ C)
    (hs : 0 ≤ s) (hsQ : ENNReal.ofReal s * Q < 1)
    (hb : ∀ x, ∃ e, x ∈ box e ∧ ‖f x‖ ≤ C * s ^ e) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  set g : ℕ → X → ℝ≥0∞ := fun e =>
    (box e).indicator (fun _ => ENNReal.ofReal C * ENNReal.ofReal s ^ e) with hg
  have hpt : ∀ x, ‖f x‖ₑ ≤ ∑' e, g e x := by
    intro x
    obtain ⟨e, hxe, hfx⟩ := hb x
    calc
      ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (C * s ^ e) := ENNReal.ofReal_le_ofReal hfx
      _ = g e x := by
        simp only [hg]
        rw [Set.indicator_of_mem hxe, ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hs]
      _ ≤ ∑' e, g e x := ENNReal.le_tsum (f := fun e => g e x) e
  have hmeas : ∀ e, AEMeasurable (g e) μ := fun e =>
    (measurable_const.indicator (hbox e)).aemeasurable
  rw [HasFiniteIntegral]
  calc
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ∫⁻ x, ∑' e, g e x ∂μ := lintegral_mono hpt
    _ = ∑' e, ∫⁻ x, g e x ∂μ := lintegral_tsum hmeas
    _ = ∑' e, ENNReal.ofReal C * ENNReal.ofReal s ^ e * μ (box e) := by
      congr 1
      funext e
      simp only [hg]
      rw [lintegral_indicator_const (hbox e)]
    _ ≤ ∑' e, ENNReal.ofReal C * M * (ENNReal.ofReal s * Q) ^ e := by
      refine ENNReal.tsum_le_tsum fun e => ?_
      calc
        ENNReal.ofReal C * ENNReal.ofReal s ^ e * μ (box e) ≤
            ENNReal.ofReal C * ENNReal.ofReal s ^ e * (M * Q ^ e) := by
          gcongr
          exact hμ e
        _ = ENNReal.ofReal C * M * (ENNReal.ofReal s * Q) ^ e := by
          rw [mul_pow]
          ring
    _ = ENNReal.ofReal C * M * (1 - ENNReal.ofReal s * Q)⁻¹ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ∞ := by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM.lt_top) ?_
      rw [ENNReal.inv_lt_top]
      exact tsub_pos_of_lt hsQ

end Abstract

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance boxFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance boxFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance boxFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The box `{x : ϖ^e x_(ab) ∈ O}` of a rectangular matrix space. -/
def box (j l e : ℕ) : Set (Matrix (Fin j) (Fin l) F.Carrier) :=
  {x | ∀ a b, (F.canonicalTopologicalData.uniformizer : F.Carrier) ^ e * x a b ∈
    F.canonicalTopologicalData.Integers}

theorem box_eq_pi (j l e : ℕ) :
    box F j l e = Set.univ.pi fun _ : Fin j => Set.univ.pi fun _ : Fin l =>
      (fun z : F.Carrier => (F.canonicalTopologicalData.uniformizer : F.Carrier) ^ e * z) ⁻¹'
        (F.canonicalTopologicalData.Integers : Set F.Carrier) := by
  ext x
  exact ⟨fun hx a _ b _ => hx a b, fun hx a b => hx a trivial b trivial⟩

variable [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]

theorem measurableSet_box (j l e : ℕ) : MeasurableSet (box F j l e) := by
  rw [box_eq_pi]
  refine MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => ?_
  exact (F.canonicalTopologicalData.isOpen_integers.preimage
    (continuous_const.mul continuous_id)).measurableSet

/-- The scalar lattice `ϖ^(-e) O` has measure `q^e μ(O)`. -/
theorem measure_preimage_uniformizer_pow_mul (μ : Measure F.Carrier) [μ.IsAddHaarMeasure]
    (e : ℕ) :
    μ ((fun z : F.Carrier => (F.canonicalTopologicalData.uniformizer : F.Carrier) ^ e * z) ⁻¹'
        (F.canonicalTopologicalData.Integers : Set F.Carrier)) =
      (F.canonicalTopologicalData.residueCardinality : ℝ≥0∞) ^ e *
        μ (F.canonicalTopologicalData.Integers : Set F.Carrier) := by
  set T := F.canonicalTopologicalData
  set a : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit T ^ e with ha
  have hcoe : ((a : F.Carrierˣ) : F.Carrier) = (T.uniformizer : F.Carrier) ^ e := by
    rw [ha, Units.val_pow_eq_pow_val, LocalFactor.PadicAbelian.uniformizerUnit_coe]
  have hscale := HarmonicAnalysis.padicScalarHaarScaling F T μ a
  have hmeas : Measurable fun z : F.Carrier => (a : F.Carrier) * z :=
    (continuous_const.mul continuous_id).measurable
  have hO : MeasurableSet (T.Integers : Set F.Carrier) := T.isOpen_integers.measurableSet
  have hmap := congrArg (fun ν : Measure F.Carrier => ν (T.Integers : Set F.Carrier)) hscale
  rw [Measure.map_apply hmeas hO, Measure.smul_apply, hcoe] at hmap
  rw [hmap]
  have hnorm : ((T.normalizedAbsUnits a : ℝ≥0)⁻¹ : ℝ≥0) =
      (T.residueCardinality : ℝ≥0) ^ e := by
    apply NNReal.eq
    rw [NNReal.coe_inv, T.normalizedAbsUnits_coe, ha, ← zpow_natCast,
      LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs, NNReal.coe_pow, NNReal.coe_natCast,
      zpow_neg, inv_inv, zpow_natCast]
  rw [ENNReal.smul_def, hnorm, smul_eq_mul, ENNReal.coe_pow, ENNReal.coe_natCast]

/-- The measure of a box of a rectangular matrix space. -/
theorem rectangularMeasure_box (μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier)
    [SigmaFinite μ.measure] (j l e : ℕ) :
    rectangularMeasure μ j l (box F j l e) =
      (μ.measure (F.canonicalTopologicalData.Integers : Set F.Carrier) ^ (j * l)) *
        ((F.canonicalTopologicalData.residueCardinality : ℝ≥0∞) ^ (j * l)) ^ e := by
  rw [box_eq_pi]
  change (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin l => μ.measure)) :
    Measure (Fin j → Fin l → F.Carrier)) _ = _
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    measure_preimage_uniformizer_pow_mul F μ.measure e]
  rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul, mul_comm, Nat.mul_comm l j, Nat.mul_comm e]

end Padic

end Langlands.RankinSelberg.TwoBlockConvergence
