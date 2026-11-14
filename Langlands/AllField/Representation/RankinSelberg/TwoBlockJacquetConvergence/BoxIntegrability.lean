import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
/-!
# Integrability from geometric bounds on an exhaustion by boxes

A measurable function `f` is integrable as soon as there are measurable sets `box e`
with `μ(box e) ≤ M Q^e` and, for every point `x`, some `e` with `x ∈ box e` and
`|f x| ≤ C s^e`, where `s Q < 1`: then `|f| ≤ ∑_e C s^e 1_(box e)`, whose integral
is a convergent geometric series. On a rectangular matrix space over a p-adic field the
boxes `{x : ϖ^e x_(ab) ∈ O}` have measure `(q^e μ(O))^(jl)` by the scalar Haar scaling.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi measurableSet_box measure_preimage_uniformizer_pow_mul rectangularMeasure_box
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open scoped ENNReal NNReal

universe u uF

section Abstract


end Abstract

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The box `{x : ϖ^e x_(ab) ∈ O}` of a rectangular matrix space. -/
def box (j l e : ℕ) : Set (Matrix (Fin j) (Fin l) F) :=
  {x | ∀ a b, ((⟨⟩ : LocalFieldData F).uniformizer : F) ^ e * x a b ∈
    (⟨⟩ : LocalFieldData F).Integers}

theorem box_eq_pi (j l e : ℕ) :
    box F j l e = Set.univ.pi fun _ : Fin j => Set.univ.pi fun _ : Fin l =>
      (fun z : F => ((⟨⟩ : LocalFieldData F).uniformizer : F) ^ e * z) ⁻¹'
        ((⟨⟩ : LocalFieldData F).Integers : Set F) := by
  ext x
  exact ⟨fun hx a _ b _ => hx a b, fun hx a b => hx a trivial b trivial⟩

variable [MeasurableSpace F] [BorelSpace F]

theorem measurableSet_box (j l e : ℕ) : MeasurableSet (box F j l e) := by
  rw [box_eq_pi]
  refine MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => ?_
  exact ((⟨⟩ : LocalFieldData F).isOpen_integers.preimage
    (continuous_const.mul continuous_id)).measurableSet

/-- The scalar lattice `ϖ^(-e) O` has measure `q^e μ(O)`. -/
theorem measure_preimage_uniformizer_pow_mul (μ : Measure F) [μ.IsAddHaarMeasure]
    (e : ℕ) :
    μ ((fun z : F => ((⟨⟩ : LocalFieldData F).uniformizer : F) ^ e * z) ⁻¹'
        ((⟨⟩ : LocalFieldData F).Integers : Set F)) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ≥0∞) ^ e *
        μ ((⟨⟩ : LocalFieldData F).Integers : Set F) := by
  set T := (⟨⟩ : LocalFieldData F)
  set a : Fˣ := Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ e with ha
  have hcoe : ((a : Fˣ) : F) = (T.uniformizer : F) ^ e := by
    rw [ha, Units.val_pow_eq_pow_val, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe]
  have hscale := Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling F T μ a
  have hmeas : Measurable fun z : F => (a : F) * z :=
    (continuous_const.mul continuous_id).measurable
  have hO : MeasurableSet (T.Integers : Set F) := T.isOpen_integers.measurableSet
  have hmap := congrArg (fun ν : Measure F => ν (T.Integers : Set F)) hscale
  rw [Measure.map_apply hmeas hO, Measure.smul_apply, hcoe] at hmap
  rw [hmap]
  have hnorm : ((T.normalizedAbsUnits a : ℝ≥0)⁻¹ : ℝ≥0) =
      (T.residueCardinality : ℝ≥0) ^ e := by
    apply NNReal.eq
    rw [NNReal.coe_inv, T.normalizedAbsUnits_coe, ha, ← zpow_natCast,
      Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs, NNReal.coe_pow, NNReal.coe_natCast,
      zpow_neg, inv_inv, zpow_natCast]
  rw [ENNReal.smul_def, hnorm, smul_eq_mul, ENNReal.coe_pow, ENNReal.coe_natCast]

/-- The measure of a box of a rectangular matrix space. -/
theorem rectangularMeasure_box (μ : HarmonicAnalysis.AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] (j l e : ℕ) :
    rectangularMeasure μ j l (box F j l e) =
      (μ.measure ((⟨⟩ : LocalFieldData F).Integers : Set F) ^ (j * l)) *
        (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ≥0∞) ^ (j * l)) ^ e := by
  rw [box_eq_pi]
  change (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin l => μ.measure)) :
    Measure (Fin j → Fin l → F)) _ = _
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    measure_preimage_uniformizer_pow_mul F μ.measure e]
  rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul, mul_comm, Nat.mul_comm l j, Nat.mul_comm e]

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockConvergence
