import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Mathlib.Algebra.Polynomial.Monic

/-! # Number-field coefficient approximation with fixed constant term -/

noncomputable section

open Polynomial NumberField

namespace Langlands.Global

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- Simultaneous coefficient approximation with prescribed degree and constant term. -/
theorem exists_monic_polynomial_approximation
    (d : ℕ) (hd : 0 < d) (c : F) (S : Finset (FinitePlace F))
    (p : ∀ v : S, (FiniteCompletion F v.val)[X])
    (q : ∀ w : InfinitePlace F, w.Completion[X])
    (hp : ∀ v, (p v).Monic ∧ (p v).natDegree = d ∧
      (p v).coeff 0 = algebraMap F (FiniteCompletion F v.val) c)
    (hq : ∀ w, (q w).Monic ∧ (q w).natDegree = d ∧
      (q w).coeff 0 = algebraMap F w.Completion c)
    (ε : S → ℝ) (η : InfinitePlace F → ℝ) (hε : ∀ v, 0 < ε v) (hη : ∀ w, 0 < η w) :
    ∃ g : F[X], g.Monic ∧ g.natDegree = d ∧ g.coeff 0 = c ∧
      (∀ (v : S) (i : ℕ), ‖(g.map (algebraMap F (FiniteCompletion F v.val))).coeff i -
        (p v).coeff i‖ < ε v) ∧
      (∀ (w : InfinitePlace F) (i : ℕ), ‖(g.map (algebraMap F w.Completion)).coeff i -
        (q w).coeff i‖ < η w) := by
  classical
  have happrox (i : ℕ) : ∃ x : F,
      (∀ v : S, ‖algebraMap F (FiniteCompletion F v.val) x - (p v).coeff i‖ < ε v) ∧
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion x - (q w).coeff i‖ < η w) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      AdelicFunctoriality.exists_algebraMap_mem_open S
        (fun v => Metric.ball ((p v).coeff i) (ε v)) (fun _ => Metric.isOpen_ball)
        (fun v => ⟨_, Metric.mem_ball_self (hε v)⟩)
        (fun w => Metric.ball ((q w).coeff i) (η w)) (fun _ => Metric.isOpen_ball)
        (fun w => ⟨_, Metric.mem_ball_self (hη w)⟩)
  choose b hbp hbq using happrox
  let a (i : ℕ) := if i = 0 then c else b i
  let r := ∑ i ∈ Finset.range d, monomial i (a i)
  let g : F[X] := X ^ d + r
  have hr : r.natDegree < d := by
    refine (natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)).trans_lt (by omega : d - 1 < d)
    have hi' := Finset.mem_range.mp hi
    exact (natDegree_monomial_le _).trans (by omega : i ≤ d - 1)
  have hgcoef (i : ℕ) : g.coeff i = (if i = d then 1 else 0) + (if i < d then a i else 0) := by
    simp [g, r, coeff_X_pow, coeff_monomial]
  have hdeg : g.natDegree = d := by
    change (X ^ d + r).natDegree = d
    rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hr), natDegree_X_pow]
  have hm : g.Monic := by
    rw [Monic, leadingCoeff, hdeg, hgcoef]
    simp
  have hconst : g.coeff 0 = c := by simp [hgcoef, a, hd, hd.ne]
  have hnear {K : Type u} [NormedField K] [Algebra F K] (f : K[X]) (hf : f.Monic)
      (hfd : f.natDegree = d) (hf0 : f.coeff 0 = algebraMap F K c) (e : ℝ) (he : 0 < e)
      (hb : ∀ i, ‖algebraMap F K (b i) - f.coeff i‖ < e) (i : ℕ) :
      ‖(g.map (algebraMap F K)).coeff i - f.coeff i‖ < e := by
    rcases lt_trichotomy i d with hi | rfl | hi
    · by_cases hi0 : i = 0
      · subst i
        simpa only [coeff_map, hconst, hf0, sub_self, norm_zero] using he
      · simpa only [coeff_map, hgcoef, hi, hi.ne, ite_false, ite_true, zero_add, a, hi0] using hb i
    · rw [coeff_map, hgcoef, ite_eq_left rfl, ite_eq_right (lt_irrefl _), add_zero, map_one,
        ← hfd, hf.coeff_natDegree, sub_self, norm_zero]
      exact he
    · rw [coeff_map, coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hi),
        coeff_eq_zero_of_natDegree_lt (hfd.symm ▸ hi), map_zero, sub_self, norm_zero]
      exact he
  exact ⟨g, hm, hdeg, hconst,
    fun v => hnear (p v) (hp v).1 (hp v).2.1 (hp v).2.2 (ε v) (hε v) (fun i => hbp i v),
    fun w => hnear (q w) (hq w).1 (hq w).2.1 (hq w).2.2 (η w) (hη w) (fun i => hbq i w)⟩

/-- Monic polynomial approximation in the actual number-field completions. -/
def NumberFieldPolynomialApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (d : ℕ), 0 < d →
    ∀ (c : F) (S : Finset (FinitePlace F))
      (p : ∀ v : S, (FiniteCompletion F v.val)[X]) (q : ∀ w : InfinitePlace F, w.Completion[X]),
    (∀ v, (p v).Monic ∧ (p v).natDegree = d ∧
      (p v).coeff 0 = algebraMap F (FiniteCompletion F v.val) c) →
    (∀ w, (q w).Monic ∧ (q w).natDegree = d ∧ (q w).coeff 0 = algebraMap F w.Completion c) →
    ∀ (ε : S → ℝ) (η : InfinitePlace F → ℝ), (∀ v, 0 < ε v) → (∀ w, 0 < η w) →
    ∃ g : F[X], g.Monic ∧ g.natDegree = d ∧ g.coeff 0 = c ∧
      (∀ (v : S) (i : ℕ), ‖(g.map (algebraMap F (FiniteCompletion F v.val))).coeff i -
        (p v).coeff i‖ < ε v) ∧
      (∀ (w : InfinitePlace F) (i : ℕ), ‖(g.map (algebraMap F w.Completion)).coeff i -
        (q w).coeff i‖ < η w)

/-- Choose the middle coefficients by weak approximation in the specified places. -/
theorem numberFieldPolynomialApproximation : NumberFieldPolynomialApproximationStatement.{u} := by
  intro F _ _ d hd c S p q hp hq ε η hε hη
  exact exists_monic_polynomial_approximation d hd c S p q hp hq ε η hε hη

end Langlands.Global
