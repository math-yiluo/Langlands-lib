import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Algebraic closures of fields isomorphic to the real numbers -/

noncomputable section

universe u v

open Polynomial

namespace Langlands.FieldTheory

variable {K : Type u} [Field K]

/-- A splitting field of the polynomial `X² + 1` contains a square root of `-1`. -/
theorem exists_sq_eq_neg_one_splittingField (K : Type u) [Field K] :
    ∃ i : (X ^ 2 + C (1 : K)).SplittingField, i ^ 2 = -1 := by
  let p : K[X] := X ^ 2 + C 1
  have hd : (p.map (algebraMap K p.SplittingField)).degree ≠ 0 := by
    apply degree_ne_of_natDegree_ne
    simp [p]
  obtain ⟨i, hi⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero hd
  exact ⟨i, add_eq_zero_iff_eq_neg.mp (by simpa [p] using hi)⟩

/-- The algebraic closure of a field isomorphic to `ℝ` has degree two. -/
theorem finrank_algebraicClosure_of_equiv_real (e : K ≃+* ℝ) :
    Module.finrank K (AlgebraicClosure K) = 2 := by
  let : Algebra K ℂ := ((algebraMap ℝ ℂ).comp e.toRingHom).toAlgebra
  let f : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) zero_lt_two
  have hi' : f i ^ 2 = Complex.I ^ 2 := by
    rw [Complex.I_sq, ← map_pow, hi, map_neg, map_one]
  have hI : ∃ j, f j = Complex.I := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi' with h | h
    · exact ⟨i, h⟩
    · exact ⟨-i, by rw [map_neg, h, neg_neg]⟩
  obtain ⟨j, hj⟩ := hI
  have hs : Function.Surjective f := by
    intro z
    refine ⟨algebraMap K _ (e.symm z.re) + algebraMap K _ (e.symm z.im) * j, ?_⟩
    rw [map_add, map_mul, f.commutes, f.commutes, hj]
    change ((e (e.symm z.re) : ℝ) : ℂ) + (e (e.symm z.im) : ℝ) * Complex.I = z
    rw [e.apply_symm_apply, e.apply_symm_apply, Complex.re_add_im]
  let g : AlgebraicClosure K ≃ₐ[K] ℂ := AlgEquiv.ofBijective f ⟨f.injective, hs⟩
  have hg : (algebraMap ℝ ℂ).comp e.toRingHom =
      g.toRingEquiv.toRingHom.comp (algebraMap K (AlgebraicClosure K)) :=
    RingHom.ext fun x => (g.commutes x).symm
  exact (Algebra.finrank_eq_of_equiv_equiv e g.toRingEquiv hg).trans Complex.finrank_real_complex

/-- Every algebra containing a square root of `-1` receives the algebraic
closure of a base field isomorphic to `ℝ`. -/
theorem nonempty_algHom_algebraicClosure_of_sq_eq_neg_one (e : K ≃+* ℝ)
    {A : Type v} [CommRing A] [Algebra K A] {i : A} (hi : i ^ 2 = -1) :
    Nonempty (AlgebraicClosure K →ₐ[K] A) := by
  let p : K[X] := X ^ 2 + C 1
  have hd : p.natDegree = 2 := natDegree_X_pow_add_C
  have hm : p.Monic := leadingCoeff_X_pow_add_C zero_lt_two
  let : Fact (Irreducible p) := ⟨irreducible_of_degree_le_three_of_not_isRoot (by simp [hd])
    (fun x hx => by
      have hx' : x ^ 2 + 1 = 0 := by simpa [p, IsRoot] using hx
      have hx'' : (e x) ^ 2 + 1 = 0 := by simpa using congrArg e hx'
      linarith [sq_nonneg (e x)])⟩
  obtain ⟨j, hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) zero_lt_two
  let f : AdjoinRoot p →ₐ[K] AlgebraicClosure K :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId K _) j (by simp [p, hj])
  let : FiniteDimensional K (AdjoinRoot p) := hm.finite_adjoinRoot
  let : FiniteDimensional K (AlgebraicClosure K) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_algebraicClosure_of_equiv_real e]; decide)
  have hdim : Module.finrank K (AdjoinRoot p) = Module.finrank K (AlgebraicClosure K) := by
    rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim, hd,
      finrank_algebraicClosure_of_equiv_real e]
  let g : AdjoinRoot p ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofBijective f ⟨f.injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
        hdim).mp f.injective⟩
  let lift : AdjoinRoot p →ₐ[K] A :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId K A) i (by simp [p, hi])
  exact ⟨lift.comp g.symm.toAlgHom⟩

/-- The algebraic closure of a field isomorphic to `ℝ` has degree two and maps
to every algebra over the field containing a square root of `-1`. -/
def RealAlgebraicClosureStatement : Prop :=
  ∀ (K : Type u) [Field K], Nonempty (K ≃+* ℝ) →
    Module.finrank K (AlgebraicClosure K) = 2 ∧
    ∀ (A : Type v) [CommRing A] [Algebra K A], (∃ i : A, i ^ 2 = -1) →
      Nonempty (AlgebraicClosure K →ₐ[K] A)

theorem realAlgebraicClosure : RealAlgebraicClosureStatement.{u, v} := by
  rintro K _ ⟨e⟩
  exact ⟨finrank_algebraicClosure_of_equiv_real e,
    fun _ _ _ ⟨_, hi⟩ => nonempty_algHom_algebraicClosure_of_sq_eq_neg_one e hi⟩

end Langlands.FieldTheory
