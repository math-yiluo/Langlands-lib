import Langlands.Analysis.DominatedHolomorphicIntegral
import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Parameter holomorphy of compactly supported complex Godement sections -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Operator ENNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.GeneralLinear (determinant determinantContinuous)

variable {m : ℕ}
local notation "G" => Langlands.GeneralLinear m ℂ
local notation "G'" => Langlands.GeneralLinear (m + 1) ℂ
local notation "Rect" => Matrix (Fin m) (Fin (m + 1)) ℂ
local instance compactHolomorphicGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance compactHolomorphicGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private theorem characterWeight_radialVariation (l : ℤ) (s t : ℂ) (z : ℂˣ) :
    characterWeight (characterOfParams l s) t z =
      characterWeight (characterOfParams l 0) t z *
        Complex.exp (2 * s * (Real.log ‖(z : ℂ)‖ : ℂ)) := by
  let d := characterOfParams l s
  let d₀ := characterOfParams l 0
  have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  change (d.character z : ℂ) * normPower t z =
    ((d₀.character z : ℂ) * normPower t z) * _
  rw [d.character_eq, d₀.character_eq]
  simp only [d, d₀, characterOfParams_weight, characterOfParams_exponent, mul_zero, Complex.cpow_zero, mul_one]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le]
  ac_rfl

variable {E : Type*} [NormedAddCommGroup E]

private theorem continuous_characterWeight_family {s : E → ℂ} (hs : Continuous s) (l : ℤ) (t : ℂ) :
    Continuous (fun p : E × ℂˣ => characterWeight (characterOfParams l (s p.1)) t p.2) := by
  have he : (fun p : E × ℂˣ => characterWeight (characterOfParams l (s p.1)) t p.2) =
      fun p => characterWeight (characterOfParams l 0) t p.2 *
        Complex.exp (2 * s p.1 * (Real.log ‖(p.2 : ℂ)‖ : ℂ)) :=
    funext fun p => characterWeight_radialVariation l (s p.1) t p.2
  rw [he]
  have hlog : Continuous (fun z : ℂˣ => (Real.log ‖(z : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp (Units.continuous_val.norm.log (fun z => norm_ne_zero_iff.mpr z.ne_zero))
  exact ((continuous_characterWeight (characterOfParams l 0) t).comp continuous_snd).mul
    (((hs.comp continuous_fst).const_mul 2).mul (hlog.comp continuous_snd)).cexp

variable [NormedSpace ℂ E]

private theorem differentiable_characterWeight_family {s : E → ℂ} (hs : Differentiable ℂ s)
    (l : ℤ) (t : ℂ) (z : ℂˣ) :
    Differentiable ℂ (fun q => characterWeight (characterOfParams l (s q)) t z) := by
  have he : (fun q => characterWeight (characterOfParams l (s q)) t z) =
      fun q => characterWeight (characterOfParams l 0) t z *
        Complex.exp (2 * s q * (Real.log ‖(z : ℂ)‖ : ℂ)) :=
    funext fun q => characterWeight_radialVariation l (s q) t z
  rw [he]
  exact (differentiable_const _).mul (((hs.const_mul 2).mul_const _).cexp)

/-- Fixed compact full-row-rank support gives joint holomorphy of a Godement section
in the added exponent and any holomorphic parameters of the smaller section. -/
def ComplexGodementCompactHolomorphicStatement (m : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] : Prop :=
  ∀ (ν : Measure (Langlands.GeneralLinear m ℂ)) [IsLocallyFiniteMeasure ν]
    (l : ℤ) (s : E → ℂ), Differentiable ℂ s →
    ∀ (Φ : Matrix (Fin m) (Fin (m + 1)) ℂ → ℂ), Continuous Φ → HasCompactSupport Φ →
      (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ (f : E → Langlands.GeneralLinear m ℂ → ℂ), Continuous f.uncurry →
      (∀ h, Differentiable ℂ (fun q => f q h)) →
    ∀ g : Langlands.GeneralLinear (m + 1) ℂ,
      Differentiable ℂ (fun q => godementSection ν (characterOfParams l (s q)) Φ (f q) g)

theorem complexGodementCompactHolomorphic [FiniteDimensional ℂ E] :
    ComplexGodementCompactHolomorphicStatement m E := by
  intro ν hν l s hs Φ hΦ hΦc hfull f hfc hfd g
  let t : ℂ := (((m : ℂ) + 1) / 2)
  let K (q : E) (h : G) : ℂ := godementSectionIntegrand (characterOfParams l (s q)) Φ (f q) g h
  obtain ⟨H, hH, hsupp⟩ := exists_compact_godementSection_support hΦc hfull (isCompact_singleton (x := g))
  have hvanish (q : E) (h : G) (hh : h ∉ H) : K q h = 0 := by
    simp only [K, godementSectionIntegrand, hsupp g (mem_singleton g) h hh, zero_mul]
  have hKc : Continuous (Function.uncurry K) := by
    change Continuous (fun p : E × G =>
      Φ (p.2.val * trailingRows g.val) * f p.1 p.2⁻¹ *
        characterWeight (characterOfParams l (s p.1)) t (determinant p.2))
    have htest : Continuous (fun p : E × G => Φ (p.2.val * trailingRows g.val)) :=
      hΦ.comp ((Units.continuous_val.comp continuous_snd).matrix_mul continuous_const)
    have hsmaller : Continuous (fun p : E × G => f p.1 p.2⁻¹) :=
      hfc.comp (continuous_fst.prodMk continuous_snd.inv)
    have hdet : Continuous (fun p : E × G => (p.1, determinant p.2)) :=
      continuous_fst.prodMk (determinantContinuous.continuous.comp continuous_snd)
    have hcomp := (continuous_characterWeight_family hs.continuous l t).comp hdet
    have hweight : Continuous (fun p : E × G =>
        characterWeight (characterOfParams l (s p.1)) t (determinant p.2)) := by
      simpa only [Function.comp_def] using hcomp
    exact (htest.mul hsmaller).mul hweight
  have hKd (h : G) : Differentiable ℂ (fun q => K q h) := by
    change Differentiable ℂ (fun q => Φ (h.val * trailingRows g.val) * f q h⁻¹ *
      characterWeight (characterOfParams l (s q)) t (determinant h))
    exact ((differentiable_const _).mul (hfd h⁻¹)).mul
      (differentiable_characterWeight_family hs l t (determinant h))
  have hmeasure : ν H ≠ ∞ := hH.measure_lt_top.ne
  let ρ := ν.restrict H
  have hI : Differentiable ℂ (fun q => ∫ h, K q h ∂ρ) := by
    apply differentiableOn_univ.mp
    apply (Langlands.Analysis.dominatedHolomorphicIntegral ρ Set.univ K ?_ ?_ ?_).2
    · intro q
      exact (hKc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact ae_of_all _ fun h => (hKd h).differentiableOn
    · intro q _
      let : ProperSpace E := FiniteDimensional.proper ℂ E
      obtain ⟨C, hC⟩ := ((isCompact_closedBall q 2).prod hH).exists_bound_of_continuousOn hKc.continuousOn
      refine ⟨1, zero_lt_one, subset_univ _, fun _ => C, integrableOn_const hmeasure, ?_⟩
      filter_upwards [ae_restrict_mem hH.measurableSet] with h hh z hz
      apply hC (z, h)
      have hz' : z ∈ Metric.ball q (2 : ℝ) := by simpa using hz
      exact ⟨Metric.ball_subset_closedBall hz', hh⟩
  have htotal (q : E) : (∫ h, K q h ∂ρ) = ∫ h, K q h ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hvanish q)
  have hId : Differentiable ℂ (fun q => ∫ h, K q h ∂ν) := by
    rw [← funext htotal]
    exact hI
  unfold godementSection
  exact (differentiable_characterWeight_family hs l ((m : ℂ) / 2) (determinant g)).mul hId

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
