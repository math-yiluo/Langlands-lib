import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Approximation of unit power classes at all infinite places -/

noncomputable section

universe u

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

/-- A global unit represents the given local power classes at all infinite places. -/
def RepresentsArchimedeanUnitPowers (n : ℕ) (a : Fˣ) (x : (v : InfinitePlace F) → v.Completionˣ) : Prop :=
  ∀ v : InfinitePlace F, ∃ b : v.Completionˣ,
    Units.map (algebraMap F v.Completion) a = x v * b ^ n

private theorem exists_unit_root {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (r : Kˣ)
    (h : ∃ z : K, z ^ n = (r : K)) : ∃ b : Kˣ, b ^ n = r := by
  obtain ⟨z, hz⟩ := h
  have hz₀ : z ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn.ne'] at hz
    exact r.ne_zero hz.symm
  exact ⟨Units.mk0 z hz₀, Units.ext hz⟩

/-- Weak approximation at the infinite places realizes any tuple of actual unit power classes. -/
theorem exists_representsArchimedeanUnitPowers {n : ℕ} (hn : 0 < n)
    (x : (v : InfinitePlace F) → v.Completionˣ) : ∃ a : Fˣ, RepresentsArchimedeanUnitPowers F n a x := by
  classical
  let W (v : InfinitePlace F) : Set v.Completion := if hv : v.IsReal then
    {z | z ≠ 0 ∧ 0 < extensionEmbeddingOfIsReal hv z / extensionEmbeddingOfIsReal hv (x v)}
    else {z | z ≠ 0}
  have hW (v : InfinitePlace F) : IsOpen (W v) := by
    by_cases hv : v.IsReal
    · simp only [W, dite_eq_left hv]
      exact isOpen_ne.inter (isOpen_lt continuous_const
        ((isometry_extensionEmbeddingOfIsReal hv).continuous.div_const _))
    · simp only [W, dite_eq_right hv]
      exact isOpen_ne
  let P : Set (InfiniteAdeleRing F) := Set.univ.pi W
  have hP : IsOpen P := isOpen_set_pi Set.finite_univ fun v _ => hW v
  have hxP : (show InfiniteAdeleRing F from fun v => (x v : v.Completion)) ∈ P := by
    intro v _
    by_cases hv : v.IsReal
    · simp only [W, dite_eq_left hv, Set.mem_ofPred_eq]
      have hne : extensionEmbeddingOfIsReal hv (x v) ≠ 0 :=
        (map_ne_zero_iff _ (ringEquivRealOfIsReal hv).injective).mpr (x v).ne_zero
      exact ⟨(x v).ne_zero, by rw [div_self hne]; exact zero_lt_one⟩
    · simpa only [W, dite_eq_right hv, Set.mem_ofPred_eq] using (x v).ne_zero
  obtain ⟨a, ha⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hP ⟨_, hxP⟩
  have haW (v : InfinitePlace F) : algebraMap F v.Completion a ∈ W v := ha v (Set.mem_univ v)
  have ha₀ : a ≠ 0 := by
    intro h
    let v : InfinitePlace F := Classical.arbitrary _
    have hbad := haW v
    rw [h, map_zero] at hbad
    by_cases hv : v.IsReal
    · simp only [W, dite_eq_left hv, Set.mem_ofPred_eq] at hbad
      exact hbad.1 rfl
    · simp only [W, dite_eq_right hv, Set.mem_ofPred_eq] at hbad
      exact hbad rfl
  let a' := Units.mk0 a ha₀
  refine ⟨a', fun v => ?_⟩
  let r : v.Completionˣ := Units.map (algebraMap F v.Completion) a' / x v
  have hr : ∃ b : v.Completionˣ, b ^ n = r := by
    apply exists_unit_root hn
    by_cases hv : v.IsReal
    · let e := ringEquivRealOfIsReal hv
      have hp := haW v
      simp only [W, dite_eq_left hv, Set.mem_ofPred_eq] at hp
      have hpos : 0 < e (r : v.Completion) := by
        simp only [r, Units.val_div_eq_div_val, Units.coe_map, map_div₀]
        exact hp.2
      refine ⟨e.symm ((e (r : v.Completion)) ^ ((n : ℝ)⁻¹)), e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, Real.rpow_inv_natCast_pow hpos.le hn.ne']
    · let e := ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hv)
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e (r : v.Completion)) hn
      refine ⟨e.symm t, e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, ht]
  obtain ⟨b, hb⟩ := hr
  refine ⟨b, ?_⟩
  rw [hb, mul_comm]
  exact (div_mul_cancel _ _).symm

end Langlands.Global
