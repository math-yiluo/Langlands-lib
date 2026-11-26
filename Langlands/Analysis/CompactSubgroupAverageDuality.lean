import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Weighted left averages over compact subgroups and their duality

Let `C` be a compact subgroup of a locally compact second-countable Hausdorff group `H` and `ν`
a finite measure on `C`. For a weight `a : C → ℂ` and a function `ψ` on `H`, the left average is
`weightedAverage ν a ψ h = ∫_C a(c) ψ(c⁻¹ h) dν(c)` (a Bochner integral).

* If `a` and `ψ` are continuous, the average is continuous (`continuous_weightedAverage`).
* For every `a`, the average vanishes outside `C · tsupport ψ`, so it is compactly supported
  when `ψ` is (`hasCompactSupport_weightedAverage`).
* The average is linear in a continuous weight for fixed continuous `ψ` (`weightLinearMap`), and
  linear in a continuous `ψ` for the constant weight `1` (`averageLinearMap`). Without
  continuity (or integrability) these linearity statements can fail, since the Bochner integral
  of a non-integrable function is `0`.
* For a left-invariant `ν`, left translation by `C` passes into the weight
  (`weightedAverage_mul_left`).
* Duality (`integral_conj_weightedAverage_mul`): let `μ` be a left-invariant, s-finite measure on
  `H` that is finite on compact sets. For continuous `a` and `Φ` and continuous compactly
  supported `ψ`, Fubini's theorem and the left invariance of `μ` give
  `∫_H conj (weightedAverage ν a ψ) Φ dμ = ∫_H conj ψ(h) (∫_C conj a(c) Φ(c h) dν(c)) dμ(h)`.

The file also proves the continuity of the functional `w ↦ ∫_C conj w · Ξ dν` on `C(C, ℂ)` and
that a continuous function with `∫_C |Ξ|² dν = 0` vanishes when `ν` charges open sets. -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.CompactAverage

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [T2Space H]

/-- The left average `h ↦ ∫_C a(c) ψ(c⁻¹ h) dν(c)` of a function `ψ` on `H` over a subgroup `C`,
with weight `a` and measure `ν` on `C`. -/
def weightedAverage {C : Subgroup H} (ν : Measure C) (a : C → ℂ) (ψ : H → ℂ) (h : H) : ℂ :=
  ∫ c, a c * ψ ((c : H)⁻¹ * h) ∂ν

variable {C : Subgroup H} [CompactSpace C] (ν : Measure C) [IsFiniteMeasure ν]

theorem isCompact_subgroup : IsCompact (C : Set H) :=
  isCompact_iff_compactSpace.mpr ‹CompactSpace C›

theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {g : C → E}
    (hg : Continuous g) :
    Integrable g ν :=
  integrableOn_univ.mp (hg.continuousOn.integrableOn_compact isCompact_univ)

theorem continuous_weightedAverage {a : C → ℂ} (ha : Continuous a) {ψ : H → ℂ}
    (hψ : Continuous ψ) : Continuous (weightedAverage ν a ψ) := by
  have hc : Continuous (Function.uncurry fun (h : H) (c : C) => a c * ψ ((c : H)⁻¹ * h)) := by
    apply (ha.comp continuous_snd).mul
    exact hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)
  have := continuous_parametric_integral_of_continuous (μ := ν) hc isCompact_univ
  show Continuous fun h => ∫ c, a c * ψ ((c : H)⁻¹ * h) ∂ν
  simpa only [Measure.restrict_univ] using this

/-- The conjugate-side average `h ↦ ∫_C a(c) Φ(c h) dν(c)` of a continuous function is
continuous. -/
theorem continuous_integral_mul_left {a : C → ℂ} (ha : Continuous a) {Φ : H → ℂ}
    (hΦ : Continuous Φ) : Continuous fun h => ∫ c, a c * Φ ((c : H) * h) ∂ν := by
  have hc : Continuous (Function.uncurry fun (h : H) (c : C) => a c * Φ ((c : H) * h)) :=
    (ha.comp continuous_snd).mul
      (hΦ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst))
  have := continuous_parametric_integral_of_continuous (μ := ν) hc isCompact_univ
  simpa only [Measure.restrict_univ] using this

/-- Pairing with a fixed continuous function is a continuous functional on `C(C, ℂ)`. -/
theorem continuous_integral_conj_mul (Ξ : C(C, ℂ)) :
    Continuous fun w : C(C, ℂ) => ∫ c, (starRingEnd ℂ) (w c) * Ξ c ∂ν := by
  have hint (w : C(C, ℂ)) : Integrable (fun c => (starRingEnd ℂ) (w c) * Ξ c) ν :=
    integrable_of_continuous ν ((Complex.continuous_conj.comp w.continuous).mul Ξ.continuous)
  have hK : 0 ≤ ‖Ξ‖ * ν.real univ := mul_nonneg (norm_nonneg _) measureReal_nonneg
  apply LipschitzWith.continuous (K := ⟨‖Ξ‖ * ν.real univ, hK⟩)
  apply LipschitzWith.of_dist_le_mul
  intro w w'
  rw [dist_eq_norm, ← integral_sub (hint w) (hint w'), dist_eq_norm]
  refine (norm_integral_le_of_norm_le_const (C := ‖w - w'‖ * ‖Ξ‖)
    (Filter.Eventually.of_forall fun c => ?_)).trans (le_of_eq ?_)
  · rw [← sub_mul, ← map_sub, norm_mul, Complex.norm_conj]
    exact mul_le_mul (ContinuousMap.norm_coe_le_norm (w - w') c)
      (ContinuousMap.norm_coe_le_norm Ξ c) (norm_nonneg _) (norm_nonneg _)
  · change _ = (‖Ξ‖ * ν.real univ) * ‖w - w'‖
    ring

/-- A continuous function whose squared modulus integrates to zero against a measure that is
positive on open sets vanishes. -/
theorem eq_zero_of_integral_conj_mul_self [ν.IsOpenPosMeasure] (Ξ : C(C, ℂ))
    (h : ∫ c, (starRingEnd ℂ) (Ξ c) * Ξ c ∂ν = 0) (c : C) : Ξ c = 0 := by
  have h1 : ∫ c, ‖Ξ c‖ ^ 2 ∂ν = 0 := by
    have : ∫ c, (starRingEnd ℂ) (Ξ c) * Ξ c ∂ν = ((∫ c, ‖Ξ c‖ ^ 2 ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext c
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [this] at h
    exact_mod_cast h
  have hcont : Continuous fun c => ‖Ξ c‖ ^ 2 := Ξ.continuous.norm.pow 2
  have h2 := (integral_eq_zero_iff_of_nonneg (fun c => sq_nonneg ‖Ξ c‖)
    (integrable_of_continuous ν hcont)).mp h1
  have h3 := (hcont.ae_eq_iff_eq ν continuous_const).mp h2
  have h4 : ‖Ξ c‖ ^ 2 = 0 := congrFun h3 c
  simpa using h4

theorem weightedAverage_eq_zero_of_notMem {a : C → ℂ} {ψ : H → ℂ} {h : H}
    (hh : h ∉ (C : Set H) * tsupport ψ) : weightedAverage ν a ψ h = 0 := by
  have hz : ∀ c : C, a c * ψ ((c : H)⁻¹ * h) = 0 := by
    intro c
    have : ψ ((c : H)⁻¹ * h) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      apply hh
      exact ⟨c, c.2, _, hm, by simp⟩
    simp [this]
  simp [weightedAverage, hz]

theorem hasCompactSupport_weightedAverage (a : C → ℂ) {ψ : H → ℂ}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (weightedAverage ν a ψ) :=
  HasCompactSupport.intro ((isCompact_subgroup (C := C)).mul hψ)
    fun _ hh => weightedAverage_eq_zero_of_notMem ν hh


/-- Left translation by an element of `C` moves into the weight. -/
theorem weightedAverage_mul_left [ν.IsMulLeftInvariant] (a : C → ℂ) (ψ : H → ℂ) (c₀ : C)
    (h : H) :
    weightedAverage ν a ψ ((c₀ : H) * h) = weightedAverage ν (fun c => a (c₀ * c)) ψ h := by
  unfold weightedAverage
  rw [← integral_mul_left_eq_self (μ := ν) _ c₀]
  congr 1
  funext c
  congr 2
  simp [mul_assoc]

/-- Left translation by an element commuting with `C` moves into the averaged function. -/
theorem weightedAverage_mul_left_of_commute (a : C → ℂ) (ψ : H → ℂ) {z : H}
    (hz : ∀ c : C, Commute (c : H) z) (h : H) :
    weightedAverage ν a ψ (z * h) = weightedAverage ν a (fun x => ψ (z * x)) h := by
  unfold weightedAverage
  congr 1
  funext c
  congr 2
  rw [← mul_assoc, ← mul_assoc, ((hz c).inv_left).eq]

/-- The weighted average depends linearly on a continuous weight. -/
def weightLinearMap {ψ : H → ℂ} (hψ : Continuous ψ) : C(C, ℂ) →ₗ[ℂ] C(H, ℂ) where
  toFun a := ⟨weightedAverage ν a ψ, continuous_weightedAverage ν a.continuous hψ⟩
  map_add' a b := by
    ext h
    change ∫ c, (a c + b c) * ψ ((c : H)⁻¹ * h) ∂ν =
      (∫ c, a c * ψ ((c : H)⁻¹ * h) ∂ν) + ∫ c, b c * ψ ((c : H)⁻¹ * h) ∂ν
    have hcont (g : C(C, ℂ)) : Continuous fun c : C => g c * ψ ((c : H)⁻¹ * h) :=
      g.continuous.mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const))
    rw [← integral_add (integrable_of_continuous ν (hcont a))
      (integrable_of_continuous ν (hcont b))]
    congr 1
    funext c
    ring
  map_smul' r a := by
    ext h
    change ∫ c, (r * a c) * ψ ((c : H)⁻¹ * h) ∂ν = r * ∫ c, a c * ψ ((c : H)⁻¹ * h) ∂ν
    rw [← integral_const_mul]
    congr 1
    funext c
    ring

@[simp] theorem weightLinearMap_apply {ψ : H → ℂ} (hψ : Continuous ψ) (a : C(C, ℂ)) (h : H) :
    weightLinearMap ν hψ a h = weightedAverage ν a ψ h := rfl

/-- The unweighted average is linear on continuous functions. -/
def averageLinearMap : C(H, ℂ) →ₗ[ℂ] (H → ℂ) where
  toFun ψ := weightedAverage ν (fun _ => 1) ψ
  map_add' ψ χ := by
    funext h
    change ∫ c, 1 * (ψ ((c : H)⁻¹ * h) + χ ((c : H)⁻¹ * h)) ∂ν =
      (∫ c, 1 * ψ ((c : H)⁻¹ * h) ∂ν) + ∫ c, 1 * χ ((c : H)⁻¹ * h) ∂ν
    have hcont (g : C(H, ℂ)) : Continuous fun c : C => 1 * g ((c : H)⁻¹ * h) :=
      continuous_const.mul (g.continuous.comp (continuous_subtype_val.inv.mul continuous_const))
    rw [← integral_add (integrable_of_continuous ν (hcont ψ))
      (integrable_of_continuous ν (hcont χ))]
    congr 1
    funext c
    ring
  map_smul' r ψ := by
    funext h
    change ∫ c, 1 * (r * ψ ((c : H)⁻¹ * h)) ∂ν = r * ∫ c, 1 * ψ ((c : H)⁻¹ * h) ∂ν
    rw [← integral_const_mul]
    congr 1
    funext c
    ring

@[simp] theorem averageLinearMap_apply (ψ : C(H, ℂ)) (h : H) :
    averageLinearMap ν ψ h = weightedAverage ν (fun _ => 1) ψ h := rfl

variable (μ : Measure H) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

/-- Duality for weighted left averages: pairing the average of `ψ` with `Φ` equals pairing
`ψ` with the conjugate-weighted left average `h ↦ ∫_C conj (a c) Φ(c h) dν(c)` of `Φ`. -/
theorem integral_conj_weightedAverage_mul {a : C → ℂ} (ha : Continuous a) {ψ : H → ℂ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {Φ : H → ℂ} (hΦ : Continuous Φ) :
    ∫ h, (starRingEnd ℂ) (weightedAverage ν a ψ h) * Φ h ∂μ =
      ∫ h, (starRingEnd ℂ) (ψ h) * ∫ c, (starRingEnd ℂ) (a c) * Φ ((c : H) * h) ∂ν ∂μ := by
  have h1 : ∀ h, (starRingEnd ℂ) (weightedAverage ν a ψ h) * Φ h =
      ∫ c, (starRingEnd ℂ) (a c) * (starRingEnd ℂ) (ψ ((c : H)⁻¹ * h)) * Φ h ∂ν := by
    intro h
    rw [weightedAverage, ← integral_conj, ← integral_mul_const]
    congr 1
    funext c
    simp [map_mul]
  have hint1 : Integrable (Function.uncurry fun (h : H) (c : C) =>
      (starRingEnd ℂ) (a c) * (starRingEnd ℂ) (ψ ((c : H)⁻¹ * h)) * Φ h) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.mul
      · apply Continuous.mul
        · exact Complex.continuous_conj.comp (ha.comp continuous_snd)
        · exact Complex.continuous_conj.comp (hψ.comp
            ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst))
      · exact hΦ.comp continuous_fst
    · apply HasCompactSupport.intro
        (((isCompact_subgroup (C := C)).mul hψc).prod isCompact_univ)
      rintro ⟨h, c⟩ hhc
      have hz : ψ ((c : H)⁻¹ * h) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        apply hhc
        exact ⟨⟨c, c.2, _, hm, by simp⟩, mem_univ _⟩
      simp [hz]
  have hint2 : Integrable (Function.uncurry fun (h : H) (c : C) =>
      (starRingEnd ℂ) (a c) * ((starRingEnd ℂ) (ψ h) * Φ ((c : H) * h))) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.mul
      · exact Complex.continuous_conj.comp (ha.comp continuous_snd)
      · apply Continuous.mul
        · exact Complex.continuous_conj.comp (hψ.comp continuous_fst)
        · exact hΦ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
    · apply HasCompactSupport.intro (hψc.prod isCompact_univ)
      rintro ⟨h, c⟩ hhc
      have hz : ψ h = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact hhc ⟨hm, mem_univ _⟩
      simp [hz]
  calc ∫ h, (starRingEnd ℂ) (weightedAverage ν a ψ h) * Φ h ∂μ
      = ∫ h, ∫ c, (starRingEnd ℂ) (a c) * (starRingEnd ℂ) (ψ ((c : H)⁻¹ * h)) * Φ h ∂ν ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ c, ∫ h, (starRingEnd ℂ) (a c) * (starRingEnd ℂ) (ψ ((c : H)⁻¹ * h)) * Φ h ∂μ ∂ν :=
        integral_integral_swap hint1
    _ = ∫ c, ∫ h, (starRingEnd ℂ) (a c) * ((starRingEnd ℂ) (ψ h) * Φ ((c : H) * h)) ∂μ ∂ν := by
        congr 1
        funext c
        rw [← integral_mul_left_eq_self (μ := μ) _ (c : H)]
        congr 1
        funext h
        simp only [inv_mul_cancel_left]
        ring
    _ = ∫ h, ∫ c, (starRingEnd ℂ) (a c) * ((starRingEnd ℂ) (ψ h) * Φ ((c : H) * h)) ∂ν ∂μ :=
        (integral_integral_swap hint2).symm
    _ = ∫ h, (starRingEnd ℂ) (ψ h) * ∫ c, (starRingEnd ℂ) (a c) * Φ ((c : H) * h) ∂ν ∂μ := by
        congr 1
        funext h
        rw [← integral_const_mul]
        congr 1
        funext c
        ring

end Langlands.Analysis.CompactAverage
