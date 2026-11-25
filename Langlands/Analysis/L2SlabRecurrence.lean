import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Weighted `L²` estimates for one-sided translation recurrences

The single-height step of Bernstein–Lapid §7.5, with a sufficient coefficient
bound in place of the sharp root bound, and a slab exhaustion for §7.6.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis

open MeasureTheory Set Filter
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A measurable shift that increases a real height by one and rescales the
measure on preimages by the square of a positive factor. -/
structure L2RenormalizingShift (μ : Measure X) where
  shift : X → X
  measurable_shift : Measurable shift
  height : X → ℝ
  measurable_height : Measurable height
  height_shift : ∀ x, height (shift x) = height x + 1
  factor : ℝ≥0
  factor_pos : 0 < factor
  map_shift : Measure.map shift μ = factor ^ (2 : ℕ) • μ

namespace L2RenormalizingShift

variable (H : L2RenormalizingShift μ)

/-- The slab where the height lies in `(a,b]`. -/
def slab (a b : ℝ) : Set X := H.height ⁻¹' Ioc a b

/-- The domain where the height is positive. -/
def positive : Set X := H.height ⁻¹' Ioi 0

protected theorem measurable_slab (a b : ℝ) : MeasurableSet (H.slab a b) :=
  H.measurable_height measurableSet_Ioc

protected theorem slab_subset_positive (a b : ℝ) (ha : 0 ≤ a) : H.slab a b ⊆ H.positive :=
  fun _ hx => ha.trans_lt hx.1

theorem height_iterate (k : ℕ) (x : X) : H.height (H.shift^[k] x) = H.height x + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', H.height_shift, ih, Nat.cast_succ, add_assoc]

theorem map_iterate (k : ℕ) : Measure.map (H.shift^[k]) μ = (H.factor ^ k) ^ (2 : ℕ) • μ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', ← Measure.map_map H.measurable_shift (H.measurable_shift.iterate k),
      ih, Measure.map_smul _ H.measurable_shift.aemeasurable, H.map_shift, smul_smul,
      pow_succ H.factor k, mul_pow]

variable {E : Type*} [NormedAddCommGroup E] {f : X → E}

/-- Change of variables for iterates on the preimage of any measurable set. -/
theorem eLpNorm_iterate_preimage (hf : StronglyMeasurable f) (k : ℕ) {S : Set X}
    (hS : MeasurableSet S) :
    eLpNorm (f ∘ H.shift^[k]) 2 (μ.restrict ((H.shift^[k]) ⁻¹' S)) =
      (H.factor : ℝ≥0∞) ^ k * eLpNorm f 2 (μ.restrict S) := by
  have hmeas := H.measurable_shift.iterate k
  rw [← eLpNorm_map_measure hf.aestronglyMeasurable hmeas.aemeasurable,
    ← Measure.restrict_map hmeas hS, H.map_iterate, Measure.restrict_smul,
    eLpNorm_smul_measure_of_ne_top' (by norm_num) _ _ hf.aestronglyMeasurable]
  have hpow : ((H.factor ^ k) ^ (2 : ℕ)) ^ (2 : ℝ≥0∞).toReal⁻¹ = H.factor ^ k := by
    rw [show (2 : ℝ≥0∞).toReal⁻¹ = (2 : ℝ)⁻¹ by norm_num,
      ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
  rw [hpow, ENNReal.smul_def, ENNReal.coe_pow, smul_eq_mul]

/-- Exact scaled norm of the pullback on a slab. -/
theorem eLpNorm_iterate_slab (hf : StronglyMeasurable f) (a b : ℝ) (k : ℕ) :
    eLpNorm (f ∘ H.shift^[k]) 2 (μ.restrict (H.slab a b)) =
      (H.factor : ℝ≥0∞) ^ k * eLpNorm f 2 (μ.restrict (H.slab (a + k) (b + k))) := by
  have hpre : (H.shift^[k]) ⁻¹' H.slab (a + k) (b + k) = H.slab a b := by
    ext x
    simp [slab, H.height_iterate]
  rw [← hpre]
  exact H.eLpNorm_iterate_preimage hf k (H.measurable_slab _ _)

/-- Square-integrability of a pullback on a slab is equivalent to that of the
original function on the translated slab. -/
theorem memLp_iterate_slab_iff (hf : StronglyMeasurable f) (a b : ℝ) (k : ℕ) :
    MemLp (f ∘ H.shift^[k]) 2 (μ.restrict (H.slab a b)) ↔
      MemLp f 2 (μ.restrict (H.slab (a + k) (b + k))) := by
  simp only [memLp_iff, H.eLpNorm_iterate_slab hf]
  constructor
  · intro h
    by_contra! hn
    rw [top_le_iff.mp hn, ENNReal.mul_top] at h
    · exact (lt_irrefl _ h)
    · exact pow_ne_zero k (ENNReal.coe_ne_zero.mpr H.factor_pos.ne')
  · intro h
    exact ENNReal.mul_lt_top (by simp) h

theorem lpNorm_iterate_slab (hf : StronglyMeasurable f) (a b : ℝ) (k : ℕ) :
    lpNorm (f ∘ H.shift^[k]) 2 (μ.restrict (H.slab a b)) =
      (H.factor : ℝ) ^ k * lpNorm f 2 (μ.restrict (H.slab (a + k) (b + k))) := by
  simp [← toReal_eLpNorm, H.eLpNorm_iterate_slab hf, ENNReal.toReal_mul, ENNReal.toReal_pow]

private theorem apply_slab_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : MemLp f 2 (μ.restrict (H.slab a b))) (h₂ : MemLp f 2 (μ.restrict (H.slab b c))) :
    MemLp f 2 (μ.restrict (H.slab a c)) ∧
      lpNorm f 2 (μ.restrict (H.slab a c)) ≤
        lpNorm f 2 (μ.restrict (H.slab a b)) + lpNorm f 2 (μ.restrict (H.slab b c)) := by
  have hd : Disjoint (H.slab a b) (H.slab b c) :=
    disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  have hu : H.slab a b ∪ H.slab b c = H.slab a c := by
    simp only [slab, ← preimage_union, Ioc_union_Ioc_eq_Ioc hab hbc]
  have hi : (H.slab a c).indicator f = (H.slab a b).indicator f + (H.slab b c).indicator f := by
    rw [← hu, indicator_union_of_disjoint hd]
    rfl
  have hm₁ := (memLp_indicator_iff_restrict (H.measurable_slab a b).nullMeasurableSet).2 h₁
  have hm₂ := (memLp_indicator_iff_restrict (H.measurable_slab b c).nullMeasurableSet).2 h₂
  refine ⟨(memLp_indicator_iff_restrict (H.measurable_slab a c).nullMeasurableSet).1 (hi ▸ hm₁.add hm₂), ?_⟩
  have hnorm (l r : ℝ) : lpNorm ((H.slab l r).indicator f) 2 μ =
      lpNorm f 2 (μ.restrict (H.slab l r)) := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_indicator_eq_eLpNorm_restrict
      (H.measurable_slab _ _).nullMeasurableSet]
  rw [← hnorm a c, hi, ← hnorm a b, ← hnorm b c]
  exact lpNorm_add_le hm₁ (by norm_num)

private theorem lpNorm_restrict_le {S T : Set X} (hST : S ⊆ T) (hf : MemLp f 2 (μ.restrict T)) :
    lpNorm f 2 (μ.restrict S) ≤ lpNorm f 2 (μ.restrict T) :=
  ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f (μ.restrict_mono_set hST))

private theorem eLpNorm_restrict_le_of_exhaustion (hf : StronglyMeasurable f)
    {S : ℕ → Set X} (hm : Monotone S) (hS : ∀ n, MeasurableSet (S n))
    {M : ℝ≥0∞} (hb : ∀ n, eLpNorm f 2 (μ.restrict (S n)) ≤ M) :
    eLpNorm f 2 (μ.restrict (⋃ n, S n)) ≤ M := by
  let g (x : X) : ℝ≥0∞ := ‖f x‖ₑ ^ (2 : ℝ)
  have hgm : Measurable g := hf.enorm.pow_const _
  have hpow (ν : Measure X) : (eLpNorm f 2 ν) ^ (2 : ℝ) = ∫⁻ x, g x ∂ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable,
      ← ENNReal.rpow_mul]
    norm_num [g]
  have hU : ∫⁻ x in (⋃ n, S n), g x ∂μ = ⨆ n, ∫⁻ x in (S n), g x ∂μ := by
    simp_rw [← lintegral_indicator (MeasurableSet.iUnion hS), ← lintegral_indicator (hS _)]
    have hind : (⋃ n, S n).indicator g = ⨆ n, (S n).indicator g := by
      ext x
      rw [iSup_apply]
      by_cases hx : x ∈ ⋃ n, S n
      · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        rw [indicator_of_mem hx]
        exact le_antisymm (le_iSup_of_le n (by rw [indicator_of_mem hn]))
          (iSup_le fun n => indicator_le_self' (fun _ _ => bot_le) _)
      · rw [indicator_of_notMem hx]
        refine le_antisymm (by positivity) (iSup_le fun n => ?_)
        rw [indicator_of_notMem (fun hn => hx (mem_iUnion.mpr ⟨n, hn⟩))]
    simp_rw [hind, iSup_apply]
    exact lintegral_iSup (fun n => hgm.indicator (hS n)) (fun n m hnm =>
      indicator_le_indicator_of_subset (hm hnm) (fun _ => bot_le))
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (2 : ℝ))).mp
  rw [hpow, hU]
  exact iSup_le fun n => (hpow (μ.restrict (S n))) ▸ ENNReal.rpow_le_rpow (hb n) (by norm_num)

variable [NormedSpace ℂ E]

/-- Evaluation of a monic difference polynomial of degree `m`, with the `m`
lower coefficients given by `p`. -/
def residual {m : ℕ} (p : Fin m → ℂ) (f : X → E) : X → E :=
  f ∘ H.shift^[m] + ∑ k, p k • (f ∘ H.shift^[(k : ℕ)])

/-- The one-direction slab estimate with automatic `L²` membership. In contrast
with an estimate stated only on `L²`, this applies before the conclusion of
square-integrability is known. The coefficient inequality is sufficient, not
necessary for Bernstein–Lapid's strict embedding. -/
theorem memLp_positive_and_lpNorm_le {m : ℕ} (p : Fin m → ℂ) (hf : StronglyMeasurable f)
    (hsmall : (∑ k, ‖p k‖ * (H.factor : ℝ) ^ (k : ℕ)) < (H.factor : ℝ) ^ m)
    (hbase : MemLp f 2 (μ.restrict (H.slab 0 m)))
    (hres : MemLp (H.residual p f) 2 (μ.restrict H.positive)) :
    MemLp f 2 (μ.restrict H.positive) ∧
      lpNorm f 2 (μ.restrict H.positive) ≤
        ((H.factor : ℝ) ^ m * lpNorm f 2 (μ.restrict (H.slab 0 m)) +
          lpNorm (H.residual p f) 2 (μ.restrict H.positive)) /
          ((H.factor : ℝ) ^ m - ∑ k, ‖p k‖ * (H.factor : ℝ) ^ (k : ℕ)) := by
  let Q (n : ℕ) := μ.restrict (H.slab 0 (m + n))
  let P (n : ℕ) := μ.restrict (H.slab 0 n)
  let D := H.residual p f
  let g (k : Fin m) := p k • (f ∘ H.shift^[(k : ℕ)])
  have hD (n : ℕ) : MemLp D 2 (P n) := hres.mono_measure
    (μ.restrict_mono_set (H.slab_subset_positive _ _ le_rfl))
  have hshift {k n N : ℕ} (hle : k + n ≤ m + N) (hN : MemLp f 2 (Q N)) :
      MemLp (f ∘ H.shift^[k]) 2 (P n) := by
    apply (H.memLp_iterate_slab_iff hf 0 n k).2
    apply hN.mono_measure (μ.restrict_mono_set ?_)
    intro x hx
    refine ⟨(by positivity : 0 ≤ (0 : ℝ) + k).trans_lt hx.1, hx.2.trans ?_⟩
    exact_mod_cast (add_comm k n ▸ hle)
  have htop : f ∘ H.shift^[m] = D - ∑ k, g k := by
    simp [D, g, residual]
  have hmem (n : ℕ) : MemLp f 2 (Q n) := by
    induction n with
    | zero => simpa [Q] using hbase
    | succ n ih =>
      have hg (k : Fin m) : MemLp (g k) 2 (P (n + 1)) :=
        (hshift (k := k) (n := n + 1) (N := n) (by omega) ih).const_smul (p k)
      have htail := (H.memLp_iterate_slab_iff hf 0 (n + 1 : ℕ) m).1
        (show MemLp (f ∘ H.shift^[m]) 2 (P (n + 1)) by
          rw [htop]
          exact (hD _).sub (memLp_finsetSum' _ fun k _ => hg k))
      have htail' : MemLp f 2 (μ.restrict (H.slab m (m + (n + 1 : ℕ)))) := by
        simpa [add_comm] using htail
      exact (H.apply_slab_split (Nat.cast_nonneg m)
        (le_add_of_nonneg_right (Nat.cast_nonneg (n + 1))) hbase htail').1
  let b := lpNorm f 2 (μ.restrict (H.slab 0 m))
  let d := lpNorm D 2 (μ.restrict H.positive)
  let c : ℝ := H.factor
  let q : ℝ := ∑ k, ‖p k‖ * c ^ (k : ℕ)
  let M : ℝ := (c ^ m * b + d) / (c ^ m - q)
  have hgap : 0 < c ^ m - q := sub_pos.mpr hsmall
  have hcp : 0 ≤ c ^ m := pow_nonneg H.factor.2 _
  have hM : 0 ≤ M := div_nonneg (add_nonneg (mul_nonneg hcp lpNorm_nonneg) lpNorm_nonneg) hgap.le
  have hbound (n : ℕ) : lpNorm f 2 (Q n) ≤ M := by
    have hg (k : Fin m) : MemLp (g k) 2 (P n) :=
      (hshift (k := k) (n := n) (N := n) (by omega) (hmem n)).const_smul (p k)
    have hlow (k : Fin m) : lpNorm (g k) 2 (P n) ≤
        (‖p k‖ * c ^ (k : ℕ)) * lpNorm f 2 (Q n) := by
      change lpNorm (p k • (f ∘ H.shift^[(k : ℕ)])) 2 (μ.restrict (H.slab 0 n)) ≤ _
      rw [lpNorm_const_smul, H.lpNorm_iterate_slab hf, ← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hkn : (n : ℝ) + k ≤ (m : ℝ) + n := by
        exact_mod_cast (show n + (k : ℕ) ≤ m + n by omega)
      exact lpNorm_restrict_le (fun _ hx => ⟨(by positivity : 0 ≤ (0 : ℝ) + k).trans_lt hx.1,
        hx.2.trans hkn⟩) (hmem n)
    have hrhs : lpNorm (f ∘ H.shift^[m]) 2 (P n) ≤ d + q * lpNorm f 2 (Q n) := by
      rw [htop]
      refine (lpNorm_sub_le (hD n) (by norm_num)).trans (add_le_add ?_ ?_)
      · exact lpNorm_restrict_le (H.slab_subset_positive _ _ le_rfl) hres
      · refine (lpNorm_sum_le (fun k _ => hg k) (by norm_num)).trans ?_
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun k _ => hlow k
    have hsub : H.slab m (m + n) ⊆ H.slab 0 (m + n) := fun _ hx =>
      ⟨(Nat.cast_nonneg m).trans_lt hx.1, hx.2⟩
    have htail : MemLp f 2 (μ.restrict (H.slab m (m + n))) :=
      (hmem n).mono_measure (μ.restrict_mono_set hsub)
    have hsplit := (H.apply_slab_split (Nat.cast_nonneg m)
      (le_add_of_nonneg_right (Nat.cast_nonneg n)) hbase htail).2
    have hscale : lpNorm (f ∘ H.shift^[m]) 2 (P n) =
        c ^ m * lpNorm f 2 (μ.restrict (H.slab m (m + n))) := by
      simpa only [P, c, zero_add, add_zero, add_comm] using H.lpNorm_iterate_slab hf 0 n m
    rw [hscale] at hrhs
    apply (le_div_iff₀ hgap).2
    change lpNorm f 2 (μ.restrict (H.slab 0 (m + n))) * (c ^ m - q) ≤ c ^ m * b + d
    have hmul := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ c ^ m by positivity)
    change c ^ m * lpNorm f 2 (Q n) ≤ c ^ m * (b + lpNorm f 2 (μ.restrict (H.slab m (m + n)))) at hmul
    linarith only [hmul, hrhs]
  have hU : (⋃ n : ℕ, H.slab 0 (m + n)) = H.positive := by
    ext x
    refine ⟨fun hx => let ⟨n, hn⟩ := mem_iUnion.mp hx; hn.1, fun hx => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (H.height x)
    exact mem_iUnion.mpr ⟨n, hx, hn.trans (le_add_of_nonneg_left (Nat.cast_nonneg m))⟩
  have hb : eLpNorm f 2 (μ.restrict H.positive) ≤ ENNReal.ofReal M := by
    rw [← hU]
    refine eLpNorm_restrict_le_of_exhaustion hf (fun n k hnk x hx => ?_)
      (fun _ => H.measurable_slab _ _) fun n => ?_
    · exact ⟨hx.1, hx.2.trans (by exact_mod_cast Nat.add_le_add_left hnk m)⟩
    · rw [← ofReal_lpNorm (hmem n)]
      exact ENNReal.ofReal_le_ofReal (hbound n)
  exact ⟨memLp_iff.mpr (hb.trans_lt ENNReal.ofReal_lt_top),
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hM)⟩

end L2RenormalizingShift

universe u v

/-- A sufficient coefficient-bound form of the one-direction `L²` slab estimate,
including square-integrability when only the boundary and residual are known to be `L²`. -/
def L2SlabRecurrenceStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} (H : L2RenormalizingShift μ)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : X → E} {m : ℕ}
    (p : Fin m → ℂ), StronglyMeasurable f →
    (∑ k, ‖p k‖ * (H.factor : ℝ) ^ (k : ℕ)) < (H.factor : ℝ) ^ m →
    MemLp f 2 (μ.restrict (H.slab 0 m)) →
    MemLp (H.residual p f) 2 (μ.restrict H.positive) →
    MemLp f 2 (μ.restrict H.positive) ∧
      lpNorm f 2 (μ.restrict H.positive) ≤
        ((H.factor : ℝ) ^ m * lpNorm f 2 (μ.restrict (H.slab 0 m)) +
          lpNorm (H.residual p f) 2 (μ.restrict H.positive)) /
          ((H.factor : ℝ) ^ m - ∑ k, ‖p k‖ * (H.factor : ℝ) ^ (k : ℕ))

/-- The one-dimensional estimate and membership for renormalizing shifts. -/
theorem l2SlabRecurrence : L2SlabRecurrenceStatement.{u, v} := by
  intro X _ μ H E _ _ f m p hf hsmall hbase hres
  exact H.memLp_positive_and_lpNorm_le p hf hsmall hbase hres

end Langlands.Analysis
