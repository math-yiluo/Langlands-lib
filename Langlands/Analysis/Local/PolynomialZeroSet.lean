import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Null zero sets of multivariate polynomials -/

namespace Langlands.Analysis

open Set MeasureTheory Filter

variable {F : Type*} [Field F]

private theorem eval_fin_cases {n : ℕ} (p : MvPolynomial (Fin (n + 1)) F)
    (x : F) (y : Fin n → F) :
    ((MvPolynomial.finSuccEquiv F n p).map (MvPolynomial.eval y)).eval x =
      MvPolynomial.eval (Fin.cons x y) p := by
  conv_lhs => rw [← MvPolynomial.eval_C (f := y) x, Polynomial.eval_map_apply]
  rw [MvPolynomial.eval_polynomial_eval_finSuccEquiv, MvPolynomial.eval_C]
  rfl

variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

/-- The zero set of a nonzero polynomial on `F^n` is null for a product of a
sigma-finite measure on `F` that vanishes on singletons. -/
theorem ae_eval_ne_zero (μ : Measure F) [SigmaFinite μ] [NullSingletonClass μ]
    (n : ℕ) (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
    apply Eventually.of_forall
    intro x hx
    have hinj : Function.Injective (MvPolynomial.aeval x :
        MvPolynomial (Fin 0) F →ₐ[F] F) :=
      (MvPolynomial.aeval_injective_iff_of_isEmpty (f := x)).mpr fun _ _ h => h
    exact hp (hinj (by simpa [MvPolynomial.aeval_eq_eval] using hx))
  | succ n ih =>
    let q := MvPolynomial.finSuccEquiv F n p
    have hq : q ≠ 0 := by simpa [q] using hp
    have hn : q.coeff q.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq
    have hs : MeasurableSet {z : F × (Fin n → F) |
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0} := by
      apply IsOpen.measurableSet
      apply isOpen_compl_singleton.preimage
      have hcons : Continuous (fun z : F × (Fin n → F) =>
          (Fin.cons z.1 z.2 : Fin (n + 1) → F)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using continuous_fst
        · exact (continuous_apply j).comp continuous_snd
      exact (MvPolynomial.continuous_eval p).comp hcons
    have hprod : ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin n => μ),
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 := by
      apply (Measure.ae_prod_iff_ae_ae hs).mpr
      apply (Measure.ae_ae_comm hs).mpr
      filter_upwards [ih (q.coeff q.natDegree) hn] with y hy
      let py := q.map (MvPolynomial.eval y)
      have hpy : py ≠ 0 := by
        intro h
        apply hy
        rw [← Polynomial.coeff_map]
        change py.coeff q.natDegree = 0
        rw [h, Polynomial.coeff_zero]
      have hnull := (Polynomial.finite_setOfPred_isRoot hpy).measure_zero μ
      have hae : ∀ᵐ x ∂μ, ¬ py.IsRoot x := ae_iff.mpr (by simpa using hnull)
      filter_upwards [hae] with x hx
      rw [← eval_fin_cases]
      exact hx
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have h := (ae_map_iff he.measurable.aemeasurable hs).mp (he.map_eq.symm ▸ hprod)
    simpa [MeasurableEquiv.piFinSuccAbove, Fin.cons_self_tail] using h

end Langlands.Analysis
