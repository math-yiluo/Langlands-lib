import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.ChevalleyWarning

/-! # Coordinate polynomials and finite-field anisotropic quadratic dimension -/

noncomputable section

universe u v w

namespace Langlands.QuadraticPolynomial

open MvPolynomial

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {ι : Type w} [Fintype ι] [DecidableEq ι]
  (Q : QuadraticForm K V) (b : ι → V)

/-- The quadratic cross term, indexed by an unordered pair of coordinates. -/
def crossTerm : Sym2 ι → MvPolynomial ι K :=
  Sym2.lift ⟨fun i j => C (QuadraticMap.polar Q (b i) (b j)) * X i * X j, by
    intro i j
    dsimp only
    rw [QuadraticMap.polar_comm]
    ring⟩

/-- An actual polynomial representing a quadratic form on finite linear combinations. -/
def coordinatePolynomial : MvPolynomial ι K :=
  ∑ i, C (Q (b i)) * X i ^ 2 +
    ∑ p ∈ (Finset.univ : Finset ι).sym2 with ¬ p.IsDiag, crossTerm Q b p

omit [Fintype ι] [DecidableEq ι] in
theorem eval_crossTerm (x : ι → K) (p : Sym2 ι) :
    eval x (crossTerm Q b p) =
      QuadraticMap.polarSym2 Q (p.map (fun i => x i • b i)) := by
  refine Sym2.inductionOn p ?_
  intro i j
  simp only [crossTerm, Sym2.lift_mk, map_mul, eval_C, eval_X, Sym2.map_mk,
    QuadraticMap.polarSym2_sym2Mk, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, smul_eq_mul]
  ring

/-- Evaluation recovers the quadratic form, including in characteristic two. -/
theorem eval_coordinatePolynomial (x : ι → K) :
    eval x (coordinatePolynomial Q b) = Q (∑ i, x i • b i) := by
  rw [QuadraticMap.map_sum]
  simp only [coordinatePolynomial, map_add, map_sum, map_mul, eval_C, eval_X,
    eval_crossTerm, QuadraticMap.map_smul, smul_eq_mul, pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem crossTerm_totalDegree_le (p : Sym2 ι) :
    (crossTerm Q b p).totalDegree ≤ 2 := by
  refine Sym2.inductionOn p ?_
  intro i j
  change (C (QuadraticMap.polar Q (b i) (b j)) * X i * X j).totalDegree ≤ 2
  calc
    _ ≤ (C (QuadraticMap.polar Q (b i) (b j)) * X i).totalDegree +
        (X j : MvPolynomial ι K).totalDegree := totalDegree_mul _ _
    _ ≤ (C (QuadraticMap.polar Q (b i) (b j)) : MvPolynomial ι K).totalDegree +
        (X i : MvPolynomial ι K).totalDegree +
        (X j : MvPolynomial ι K).totalDegree :=
      Nat.add_le_add_right (totalDegree_mul _ _) _
    _ = 2 := by simp

/-- The coordinate polynomial has total degree at most two. -/
theorem coordinatePolynomial_totalDegree_le :
    (coordinatePolynomial Q b).totalDegree ≤ 2 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp)
  · apply totalDegree_finsetSum_le
    intro p _
    exact crossTerm_totalDegree_le Q b p

variable [FiniteDimensional K V] [Fintype K]

/-- Anisotropic quadratic forms over finite fields have dimension at most two. -/
theorem finiteField_finrank_le_two (hQ : Q.Anisotropic) :
    Module.finrank K V ≤ 2 := by
  classical
  by_contra hn
  have hn' : 2 < Module.finrank K V := Nat.lt_of_not_ge hn
  let b := Module.finBasis K V
  let P := coordinatePolynomial Q b
  have hz (x : Fin (Module.finrank K V) → K) : eval x P = 0 ↔ x = 0 := by
    constructor
    · intro hx
      have hs : b.equivFun.symm x = 0 := hQ _ (by
        rw [b.equivFun_symm_apply]
        exact (eval_coordinatePolynomial Q b x).symm.trans hx)
      have hx' := congrArg b.equivFun hs
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using hx'
    · rintro rfl
      change eval 0 (coordinatePolynomial Q b) = 0
      rw [eval_coordinatePolynomial]
      simp
  have hcard : Fintype.card {x : Fin (Module.finrank K V) → K // eval x P = 0} = 1 := by
    let : Unique {x : Fin (Module.finrank K V) → K // eval x P = 0} :=
      { default := ⟨0, (hz 0).mpr rfl⟩
        uniq := fun x => Subtype.ext ((hz x.1).mp x.2) }
    exact Fintype.card_unique
  have hdeg : P.totalDegree < Fintype.card (Fin (Module.finrank K V)) := by
    simpa using (coordinatePolynomial_totalDegree_le Q b).trans_lt hn'
  have hdvd := _root_.char_dvd_card_solutions (ringChar K) hdeg
  rw [hcard] at hdvd
  exact (CharP.char_is_prime K (ringChar K)).ne_one (Nat.dvd_one.mp hdvd)

end Langlands.QuadraticPolynomial
