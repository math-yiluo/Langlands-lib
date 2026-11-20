import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Group.Integral

/-! # Integrability on lines and exhaustion by compact sets in `ℝⁿ`

Two measure-theoretic facts used to restrict square-integrability on `ℝⁿ` to lines:

* if `f` is integrable on a ball around `0` and `v 0 = 1`, then for almost every `x` near `0` the
  function `t ↦ f (x + t v)` is integrable on a fixed interval `(-T, T)` (Fubini along the shear
  `(t, y) ↦ (t, y + t w)`, `v = (1, w)`);
* a nonnegative function, continuous off a closed null set `Z`, whose integrals over the compact
  subsets of `U \ Z` are bounded, is integrable on the bounded open set `U`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open MeasureTheory Metric Filter Topology Set

section Lines

variable {n : ℕ}

/-- The measurable equivalence `(Fin (n + 1) → ℝ) ≃ ℝ × (Fin n → ℝ)`, `x ↦ (x 0, tail x)`. -/
def headTailEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0

theorem headTailEquiv_apply (x : Fin (n + 1) → ℝ) : headTailEquiv n x = (x 0, Fin.tail x) := by
  ext j
  · rfl
  · simp [headTailEquiv, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]

theorem headTailEquiv_symm_apply (p : ℝ × (Fin n → ℝ)) :
    (headTailEquiv n).symm p = Fin.cons p.1 p.2 := by
  apply (headTailEquiv n).injective
  rw [MeasurableEquiv.apply_symm_apply, headTailEquiv_apply]
  simp

theorem measurePreserving_headTailEquiv : MeasurePreserving (headTailEquiv n) :=
  volume_preserving_piFinSuccAbove (fun _ => ℝ) 0

/-- The shear `(t, y) ↦ (t, y + t • w)` of `ℝ × ℝⁿ`. -/
def shear (w : Fin n → ℝ) : ℝ × (Fin n → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) where
  toFun p := (p.1, p.2 + p.1 • w)
  invFun p := (p.1, p.2 - p.1 • w)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := by
    show Measurable (fun p : ℝ × (Fin n → ℝ) => (p.1, p.2 + p.1 • w))
    fun_prop
  measurable_invFun := by
    show Measurable (fun p : ℝ × (Fin n → ℝ) => (p.1, p.2 - p.1 • w))
    fun_prop

theorem shear_apply (w : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) :
    shear w p = (p.1, p.2 + p.1 • w) :=
  rfl

theorem shear_symm_apply (w : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) :
    (shear w).symm p = (p.1, p.2 - p.1 • w) :=
  rfl

theorem measurePreserving_shear (w : Fin n → ℝ) :
    MeasurePreserving (shear w) (volume.prod volume) (volume.prod volume) := by
  have h := MeasurePreserving.skew_product (μa := (volume : Measure ℝ))
    (μc := (volume : Measure (Fin n → ℝ))) (MeasurePreserving.id volume)
    (g := fun t y => y + t • w) (by fun_prop)
    (Eventually.of_forall fun t => (measurePreserving_add_right volume (t • w)).map_eq)
  exact h

/-- **Integrability on almost every line.** Let `v 0 = 1`, `f` integrable on `ball 0 ρ`, and
`0 < T` with `4 T (1 + ‖v‖) ≤ ρ`. Then for almost every `x` with `‖x‖ < min T (ρ / (2 (1 + ‖v‖)))`,
the function `t ↦ f (x + t • v)` is integrable on `(-T, T)`. -/
theorem exists_ae_integrableOn_line (v : Fin (n + 1) → ℝ) (hv : v 0 = 1)
    {f : (Fin (n + 1) → ℝ) → ℝ} {ρ T : ℝ} (hf : IntegrableOn f (ball 0 ρ)) (hT : 0 < T)
    (hTρ : 4 * T * (1 + ‖v‖) ≤ ρ) :
    ∀ᵐ x : Fin (n + 1) → ℝ, ‖x‖ < min T (ρ / (2 * (1 + ‖v‖))) →
      IntegrableOn (fun t : ℝ => f (x + t • v)) (Ioo (-T) T) := by
  set w : Fin n → ℝ := Fin.tail v with hw
  have hwv : ‖w‖ ≤ ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => ?_
    exact norm_le_pi_norm v j.succ
  have hρ : 0 < ρ := by
    have : 0 < 4 * T * (1 + ‖v‖) := by positivity
    linarith
  -- `Φ (t, y) = (t, y + t w)` read in `ℝⁿ⁺¹`, and its inverse `Ψ`
  let Φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := (headTailEquiv n).symm ∘ shear w
  let Ψ : (Fin (n + 1) → ℝ) → ℝ × (Fin n → ℝ) := (shear w).symm ∘ headTailEquiv n
  have hΦ : MeasurePreserving Φ (volume.prod volume) volume :=
    (measurePreserving_headTailEquiv (n := n)).symm.comp (measurePreserving_shear w)
  have hΨ : MeasurePreserving Ψ volume (volume.prod volume) :=
    (measurePreserving_shear w).symm.comp (measurePreserving_headTailEquiv (n := n))
  have hΦapply : ∀ s y, Φ (s, y) = Fin.cons s (y + s • w) := by
    intro s y
    simp [Φ, headTailEquiv_symm_apply, shear_apply]
  have hΨapply : ∀ x, Ψ x = (x 0, Fin.tail x - x 0 • w) := by
    intro x
    simp [Ψ, headTailEquiv_apply, shear_symm_apply]
  -- the line through `x` in the shear coordinates
  have hline : ∀ (x : Fin (n + 1) → ℝ) (t : ℝ), Φ ((Ψ x).1 + t, (Ψ x).2) = x + t • v := by
    intro x t
    rw [hΨapply, hΦapply]
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [hv]
    · simp [hw, Fin.tail]
      ring
  -- the globalized integrand and Fubini
  set F : (Fin (n + 1) → ℝ) → ℝ := (ball (0 : Fin (n + 1) → ℝ) ρ).indicator f with hF
  have hFint : Integrable F := (integrable_indicator_iff measurableSet_ball).2 hf
  have hFΦ : Integrable (F ∘ Φ) (volume.prod volume) :=
    (hΦ.integrable_comp hFint.aestronglyMeasurable).2 hFint
  have hgood : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), Integrable (fun s : ℝ => F (Φ (s, y))) :=
    hFΦ.prod_left_ae
  set N : Set (Fin n → ℝ) := {y | ¬ Integrable (fun s : ℝ => F (Φ (s, y)))} with hN
  have hN0 : volume N = 0 := ae_iff.1 hgood
  have hbad : volume (Ψ ⁻¹' (univ ×ˢ N)) = 0 := by
    apply hΨ.quasiMeasurePreserving.preimage_null
    rw [Measure.prod_prod, hN0, mul_zero]
  set r := min T (ρ / (2 * (1 + ‖v‖))) with hr
  have hae : ∀ᵐ x : Fin (n + 1) → ℝ, x ∉ Ψ ⁻¹' (univ ×ˢ N) :=
    measure_eq_zero_iff_ae_notMem.1 hbad
  filter_upwards [hae] with x hx hxr
  have hyx : Integrable (fun s : ℝ => F (Φ (s, (Ψ x).2))) := by
    by_contra h
    exact hx ⟨mem_univ _, h⟩
  have hx0 : |x 0| < T := by
    have : |x 0| ≤ ‖x‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm x 0
    linarith [min_le_left T (ρ / (2 * (1 + ‖v‖)))]
  -- integrability of `s ↦ F (Φ (s, y_x))` on `(x 0 - T, x 0 + T)`, translated to `(-T, T)`
  have h1 : IntegrableOn (fun t : ℝ => F (Φ ((Ψ x).1 + t, (Ψ x).2))) (Ioo (-T) T) := by
    have h2 : Integrable (fun t : ℝ => F (Φ ((Ψ x).1 + t, (Ψ x).2))) :=
      hyx.comp_add_left ((Ψ x).1)
    exact h2.integrableOn
  -- on the line, `F = f`
  refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp only [hline, hF]
  rw [indicator_of_mem]
  rw [mem_ball, dist_zero_right]
  have hvn : ‖t • v‖ ≤ T * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact abs_lt.2 ⟨ht.1, ht.2⟩ |>.le
  have hrv : r * (1 + ‖v‖) ≤ ρ / 2 := by
    have h3 : r ≤ ρ / (2 * (1 + ‖v‖)) := min_le_right _ _
    have h4 : 0 < 1 + ‖v‖ := by positivity
    calc r * (1 + ‖v‖) ≤ ρ / (2 * (1 + ‖v‖)) * (1 + ‖v‖) := by gcongr
      _ = ρ / 2 := by field_simp
  calc ‖x + t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_add_le _ _
    _ < r + T * ‖v‖ := by linarith
    _ < ρ := by nlinarith [norm_nonneg v]

end Lines

section Exhaustion

variable {n : ℕ}

/-- **Exhaustion.** Let `U ⊆ ℝⁿ` be open and bounded and `Z` closed and null. If `f ≥ 0` is
continuous on `U \ Z` and `∫_A f ≤ C` for every compact `A ⊆ U` disjoint from `Z`, then `f` is
integrable on `U`. -/
theorem integrableOn_of_forall_isCompact_le {f : (Fin n → ℝ) → ℝ} {U Z : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hZ : IsClosed Z) (hZ0 : volume Z = 0)
    (hf : ContinuousOn f (U \ Z)) (hf0 : ∀ x, 0 ≤ f x) {C : ℝ}
    (hC : ∀ A : Set (Fin n → ℝ), IsCompact A → A ⊆ U → (∀ x ∈ A, x ∉ Z) → ∫ x in A, f x ≤ C) :
    IntegrableOn f U := by
  have hV : IsOpen (U \ Z) := hU.sdiff hZ
  obtain ⟨K, hKc, hKV, hKU, hKmono⟩ := hV.exists_iUnion_isClosed
  have hKcomp : ∀ j, IsCompact (K j) := fun j =>
    Metric.isCompact_of_isClosed_isBounded (hKc j) (hUb.subset ((hKV j).trans sdiff_subset))
  have hKint : ∀ j, IntegrableOn f (K j) := fun j =>
    (hf.mono (hKV j)).integrableOn_compact (hKcomp j)
  have hlint : ∀ j, ∫⁻ x in K j, ENNReal.ofReal (f x) ≤ ENNReal.ofReal C := by
    intro j
    rw [← ofReal_integral_eq_lintegral_ofReal (hKint j) (Eventually.of_forall fun x => hf0 x)]
    exact ENNReal.ofReal_le_ofReal (hC (K j) (hKcomp j) ((hKV j).trans sdiff_subset)
      fun x hx => ((hKV j) hx).2)
  have hmeasV : AEStronglyMeasurable f (volume.restrict (U \ Z)) :=
    hf.aestronglyMeasurable hV.measurableSet
  have hUV : (U \ Z : Set (Fin n → ℝ)) =ᵐ[volume] U := by
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [sdiff_eq_empty.2 sdiff_subset, measure_empty]
    · rw [sdiff_sdiff_right_self]
      exact measure_mono_null inter_subset_right hZ0
  have hVint : IntegrableOn f (U \ Z) := by
    refine ⟨hmeasV, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => hf0 x)]
    rw [← hKU, setLIntegral_iUnion_of_directed _ hKmono.directed_le]
    exact lt_of_le_of_lt (iSup_le hlint) ENNReal.ofReal_lt_top
  exact hVint.congr_set_ae hUV.symm

end Exhaustion

end Langlands.Analysis.SeveralComplex
