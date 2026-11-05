import Langlands.FieldTheory.RealValuationProlongationSeparation
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormAmbient

/-! # Descending an isolated small conjugate over a Henselian valuation ring -/

noncomputable section

open Polynomial
open scoped NNReal

namespace Langlands.FieldTheory

open Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- If one conjugate of an algebraic element is small and every other conjugate
is a unit, Hensel lifting descends that element to the original field. -/
theorem mem_range_of_small_and_other_conjugates_units
    (ν : Valuation K ℝ≥0) [HenselianLocalRing ν.valuationSubring]
    (w : Valuation Ω ℝ≥0) (hw : w.comap (algebraMap K Ω) = ν)
    (b : Ω) (hb : w b < 1)
    (hother : ∀ r ∈ (minpoly K b).aroots Ω, r ≠ b → w r = 1) :
    b ∈ Set.range (algebraMap K Ω) := by
  classical
  let f := minpoly K b
  let g := f.map (algebraMap K Ω)
  have hint : IsIntegral K b := Algebra.IsIntegral.isIntegral b
  have hf : f.Monic := minpoly.monic hint
  have hg : g.Monic := hf.map _
  have hsplit : g.Splits := Normal.splits inferInstance b
  have hroot : b ∈ g.roots := mem_aroots.mpr ⟨hf.ne_zero, minpoly.aeval K b⟩
  have hgb : g.eval b = 0 := (mem_roots hg.ne_zero).mp hroot
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable K b
  have hnodup : g.roots.Nodup := Polynomial.nodup_roots hsep.map
  have hgint : IntPoly w g := by
    rw [hsplit.eq_prod_roots_of_monic hg]
    apply IntPoly.multiset_prod_X_sub_C
    intro r hr
    by_cases hrb : r = b
    · simpa only [hrb] using hb.le
    · exact (hother r hr hrb).le
  have hnorm (a : K) : w (algebraMap K Ω a) = ν a :=
    congrArg (fun v : Valuation K ℝ≥0 => v a) hw
  have hfint : IntPoly ν f := by
    intro n
    rw [← hnorm]
    simpa only [g, coeff_map] using hgint n
  have hderb : w (g.derivative.eval b) = 1 := by
    rw [hsplit.eval_root_derivative hg hroot, map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_one
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
    have hrb : r ≠ b := fun heq => (hnodup.mem_erase_iff.mp hr).1 heq
    have hr1 := hother r (Multiset.mem_of_mem_erase hr) hrb
    rw [Function.comp_apply, w.map_sub_eq_of_lt_right (by rw [hr1]; exact hb), hr1]
  have hg0 : w (g.eval 0) < 1 := by
    have h := val_eval_sub_le hgint (a := 0) (b := b) (by simp) hb.le
    rw [hgb, sub_zero, zero_sub, Valuation.map_neg] at h
    exact h.trans_lt hb
  have hderdiff : w (g.derivative.eval b - g.derivative.eval 0) < 1 := by
    have h := val_eval_sub_le hgint.derivative (a := b) (b := 0) hb.le (by simp)
    rw [sub_zero] at h
    exact h.trans_lt hb
  have hder0 : w (g.derivative.eval 0) = 1 := by
    have h := w.map_sub_eq_of_lt_right (show
      w (g.derivative.eval b - g.derivative.eval 0) < w (g.derivative.eval b) by
        rwa [hderb])
    have heq : g.derivative.eval b - g.derivative.eval 0 - g.derivative.eval b =
        -(g.derivative.eval 0) := by ring
    rwa [heq, Valuation.map_neg, hderb] at h
  have hfe0 : ν (f.eval 0) < 1 := by
    rw [← hnorm]
    simpa only [g, ← map_zero (algebraMap K Ω), eval_map_apply] using hg0
  have hfd0 : ν (f.derivative.eval 0) = 1 := by
    rw [← hnorm]
    simpa only [g, derivative_map, ← map_zero (algebraMap K Ω), eval_map_apply] using hder0
  obtain ⟨c, hfc, hc⟩ := valHensel_of_henselian ν f hf hfint 0 (by simp) hfe0 hfd0
  have hcsmall : w (algebraMap K Ω c) < 1 := by
    rw [hnorm]
    simpa only [sub_zero] using hc
  have hgmap : g.eval (algebraMap K Ω c) = 0 := by
    rw [show g = f.map (algebraMap K Ω) from rfl, eval_map_apply, hfc, map_zero]
  refine ⟨c, ?_⟩
  exact eq_of_eval_eq_zero hgint hb.le hgb hgmap
    ((w.map_sub _ _).trans_lt (max_lt hcsmall hb)) hderb

end Langlands.FieldTheory
