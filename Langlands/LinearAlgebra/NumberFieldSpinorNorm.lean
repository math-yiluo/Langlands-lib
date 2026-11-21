import Langlands.LinearAlgebra.CliffordSpinorNorm
import Langlands.LinearAlgebra.NumberFieldQuadraticRepresentation
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Local-to-global representation of spinor norms by two values -/

noncomputable section

universe u v

namespace Langlands.QuadraticForm

open QuadraticMap NumberField
open scoped TensorProduct

private theorem exists_pos_neg_of_even_prod_neg (l : List ℝ) (he : Even l.length)
    (h : l.prod < 0) : (∃ r ∈ l, 0 < r) ∧ (∃ r ∈ l, r < 0) := by
  constructor
  · by_contra! hn
    have hp : 0 ≤ (l.map Neg.neg).prod := List.prod_nonneg fun a ha => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact neg_nonneg.mpr (hn r hr)
    rw [List.prod_map_neg, he.neg_one_pow, one_mul] at hp
    exact (not_lt_of_ge hp) h
  · by_contra! hn
    exact (not_lt_of_ge (List.prod_nonneg hn)) h

private theorem exists_represents_mul_of_real_even_values
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (e : K ≃+* ℝ) (q : QuadraticForm K V) {a : K} {x : V} (hx : q x ≠ 0)
    (l : List {v : V // q v ≠ 0}) (he : Even l.length) {t : K} (ht : t ≠ 0)
    (hl : reflectionWordValue q l = a * t ^ 2) : ∃ y, q y = a * q x := by
  have hscale (z : V) (hz : q z ≠ 0) (h : 0 ≤ e (a * q x) / e (q z)) :
      ∃ y, q y = a * q x := by
    let c := e.symm (Real.sqrt (e (a * q x) / e (q z)))
    refine ⟨c • z, e.injective ?_⟩
    rw [QuadraticMap.map_smul q, smul_eq_mul, ← pow_two c, map_mul, map_pow]
    rw [show e c = Real.sqrt (e (a * q x) / e (q z)) from e.apply_symm_apply _,
      Real.sq_sqrt h, div_mul_cancel₀ _ ((map_ne_zero e).mpr hz)]
  by_cases ha : 0 ≤ e a
  · apply hscale x hx
    rw [map_mul, mul_div_cancel_right₀ _ ((map_ne_zero e).mpr hx)]
    exact ha
  · have hprod : (l.map (fun z : {v : V // q v ≠ 0} => e (q z))).prod < 0 := by
      change ((l.map (e ∘ fun z : {v : V // q v ≠ 0} => q z)).prod) < 0
      rw [← List.map_map, ← map_list_prod, ← reflectionWordValue, hl, map_mul, map_pow]
      exact mul_neg_of_neg_of_pos (lt_of_not_ge ha) (sq_pos_of_ne_zero ((map_ne_zero e).mpr ht))
    have he' : Even (l.map (fun z : {v : V // q v ≠ 0} => e (q z))).length := by simpa using he
    obtain ⟨⟨p, hp, hp'⟩, ⟨n, hn, hn'⟩⟩ := exists_pos_neg_of_even_prod_neg _ he' hprod
    obtain ⟨positive, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨negative, _, rfl⟩ := List.mem_map.mp hn
    by_cases hxsign : 0 ≤ e (q x)
    · apply hscale negative negative.property
      rw [map_mul]
      exact div_nonneg_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hxsign)
        hn'.le
    · apply hscale positive positive.property
      rw [map_mul]
      exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (le_of_not_ge hxsign)) hp'.le

/-- An archimedean spinor-norm value of a regular number-field form of dimension at least
four is the product of two global values modulo squares. More precisely, it multiplies every
nonzero value of the form to another represented value. -/
def NumberFieldSpinorNormRepresentationStatement : Prop :=
  ∀ (F V : Type u) [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (q : QuadraticForm F V) (a : F),
    q.polarBilin.Nondegenerate → 4 ≤ Module.finrank F V →
    (∀ v : InfinitePlace F,
      let K := v.Completion
      let qv := q.baseChange K
      ∃ (l : List {y : K ⊗[F] V // qv y ≠ 0}) (t : K),
        Even l.length ∧ t ≠ 0 ∧ reflectionWordValue qv l = algebraMap F K a * t ^ 2) →
    ∀ x, q x ≠ 0 → ∃ y, q y = a * q x

/-- The archimedean criterion follows from the quadratic representation theorem. -/
theorem numberFieldSpinorNormRepresentation : NumberFieldSpinorNormRepresentationStatement.{u} := by
  intro F V _ _ _ _ _ q a hq hrank h x hx
  apply Langlands.numberFieldQuadraticRepresentation_of_archimedean q hq hrank (a * q x)
  intro v
  let K := v.Completion
  let qv := q.baseChange K
  let x' : K ⊗[F] V := 1 ⊗ₜ[F] x
  have hx' : qv x' = algebraMap F K (q x) := by
    simp [x', qv, QuadraticForm.baseChange_tmul, Algebra.smul_def]
  change ∃ y, qv y = algebraMap F K (a * q x)
  rw [map_mul, ← hx']
  by_cases hv : v.IsReal
  · let e : K ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    obtain ⟨l, t, he, ht, hl⟩ := h v
    exact exists_represents_mul_of_real_even_values e qv
      (hx'.trans_ne ((map_ne_zero (algebraMap F K)).mpr hx)) l he ht hl
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : K ≃+* ℂ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv'
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap F K a)) zero_lt_two
    have hc' : e.symm c ^ 2 = algebraMap F K a := e.injective (by simpa using hc)
    exact ⟨e.symm c • x', by rw [QuadraticMap.map_smul qv, smul_eq_mul, ← pow_two, hc']⟩

end Langlands.QuadraticForm
