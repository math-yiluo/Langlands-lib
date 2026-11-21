import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Bounded pullback between measured `L²` spaces

A reusable realization for the weighted translations and domain restrictions of
Bernstein–Lapid §§7.3–7.5. The pushforward domination takes a squared constant.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis

open MeasureTheory Filter
open scoped ENNReal NNReal

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure X} {ν : Measure Y} {φ : X → Y}

/-- Domination of a pushforward by `c² ν` bounds the pullback's `L²` norm by `c`. -/
def boundedL2Pullback (hφ : Measurable φ) (c : ℝ≥0)
    (hd : Measure.map φ μ ≤ (c : ℝ≥0∞) ^ (2 : ℕ) • ν) :
    Lp E 2 ν →L[ℂ] Lp E 2 μ := by
  let hq : Measure.QuasiMeasurePreserving φ μ ν :=
    ⟨hφ, (Measure.absolutelyContinuous_of_le hd).trans (Measure.AbsolutelyContinuous.rfl.smul_left _)⟩
  let hm (f : Lp E 2 ν) : MemLp (f ∘ φ) 2 μ :=
    ((Lp.memLp f).of_measure_le_smul (by simp) hd).comp_of_map hφ.aemeasurable
  let P (f : Lp E 2 ν) := (hm f).toLp (f ∘ φ)
  have hP (f : Lp E 2 ν) : P f =ᵐ[μ] f ∘ φ := (hm f).coeFn_toLp
  let A : Lp E 2 ν →ₗ[ℂ] Lp E 2 μ :=
    { toFun := P
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [hP (u + v), hP u, hP v, hq.ae_eq_comp (Lp.coeFn_add u v),
          Lp.coeFn_add (P u) (P v)] with x huv hu hv hsum hadd
        calc
          P (u + v) x = (u + v) (φ x) := huv
          _ = u (φ x) + v (φ x) := hsum
          _ = P u x + P v x := congrArg₂ (· + ·) hu.symm hv.symm
          _ = (P u + P v) x := hadd.symm
      map_smul' := by
        intro a u
        apply Lp.ext
        filter_upwards [hP (a • u), hP u, hq.ae_eq_comp (Lp.coeFn_smul a u),
          Lp.coeFn_smul a (P u)] with x hau hu hsmul hadd
        calc
          P (a • u) x = (a • u) (φ x) := hau
          _ = a • u (φ x) := hsmul
          _ = a • P u x := congrArg (a • ·) hu.symm
          _ = (a • P u) x := hadd.symm }
  apply A.mkContinuous c
  intro f
  change ‖P f‖ ≤ (c : ℝ) * ‖f‖
  have hle := eLpNorm_le_of_measure_le_smul (f := (f : Y → E)) (p := 2) hd
  have hpow : ((c : ℝ≥0∞) ^ (2 : ℕ)) ^ (1 / (2 : ℝ≥0∞)).toReal = (c : ℝ≥0∞) := by
    rw [show (1 / (2 : ℝ≥0∞)).toReal = (2 : ℝ)⁻¹ by norm_num [ENNReal.toReal_div],
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hpow, smul_eq_mul] at hle
  have hle' : eLpNorm (f ∘ φ) 2 μ ≤ (c : ℝ≥0∞) * eLpNorm f 2 ν :=
    (eLpNorm_map_measure (Lp.stronglyMeasurable f).aestronglyMeasurable hφ.aemeasurable).symm ▸ hle
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.coe_toReal c, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top f)) hle'

/-- The operator norm of the measured pullback is at most the scaling factor. -/
theorem norm_boundedL2Pullback_le (hφ : Measurable φ) (c : ℝ≥0)
    (hd : Measure.map φ μ ≤ (c : ℝ≥0∞) ^ (2 : ℕ) • ν) :
    ‖(boundedL2Pullback hφ c hd : Lp E 2 ν →L[ℂ] Lp E 2 μ)‖ ≤ (c : ℝ) := by
  unfold boundedL2Pullback
  exact LinearMap.mkContinuous_norm_le _ c.2 _

/-- The continuous linear pullback acts by the actual composed representative. -/
theorem boundedL2Pullback_ae (hφ : Measurable φ) (c : ℝ≥0)
    (hd : Measure.map φ μ ≤ (c : ℝ≥0∞) ^ (2 : ℕ) • ν) (f : Lp E 2 ν) :
    boundedL2Pullback hφ c hd f =ᵐ[μ] f ∘ φ :=
  MemLp.coeFn_toLp (((Lp.memLp f).of_measure_le_smul (by simp) hd).comp_of_map hφ.aemeasurable)

/-- Pull back a function that is supplied before passing to `L²` classes. -/
theorem boundedL2Pullback_toLp_ae (hφ : Measurable φ) (c : ℝ≥0)
    (hd : Measure.map φ μ ≤ (c : ℝ≥0∞) ^ (2 : ℕ) • ν)
    {f : Y → E} (hf : MemLp f 2 ν) :
    boundedL2Pullback hφ c hd (hf.toLp f) =ᵐ[μ] f ∘ φ := by
  have hq : Measure.QuasiMeasurePreserving φ μ ν :=
    ⟨hφ, (Measure.absolutelyContinuous_of_le hd).trans (Measure.AbsolutelyContinuous.rfl.smul_left _)⟩
  exact (boundedL2Pullback_ae hφ c hd _).trans (hq.ae_eq_comp hf.coeFn_toLp)

/-- Restrict an `L²` function to a measurable domain in the same ambient type. -/
def restrictL2 (S : Set X) : Lp E 2 μ →L[ℂ] Lp E 2 (μ.restrict S) :=
  boundedL2Pullback measurable_id 1 (by simpa using Measure.restrict_le_self (μ := μ) (s := S))

/-- Restriction agrees with the original representative on the restricted measure. -/
theorem restrictL2_ae (S : Set X) (f : Lp E 2 μ) : restrictL2 S f =ᵐ[μ.restrict S] f :=
  boundedL2Pullback_ae measurable_id 1 _ f

end Langlands.Analysis
