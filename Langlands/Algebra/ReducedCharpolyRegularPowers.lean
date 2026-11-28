import Langlands.Algebra.ReducedCharpolyFromSplitFactors
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.Minpoly.Field

/-! # Regular elements of central simple algebras: minimal polynomials and powers -/

noncomputable section

universe u

open Polynomial

namespace Langlands.CentralSimple

section Evaluation

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- If `g` is separable and `g(a) = 0`, then `g'(a)` is a unit. -/
theorem isUnit_aeval_derivative_of_separable {g : K[X]} (hg : g.Separable) {a : A}
    (ha : aeval a g = 0) : IsUnit (aeval a (derivative g)) := by
  obtain ⟨p, q, h⟩ := hg
  have h1 := congrArg (aeval a) h
  rw [map_add, map_mul, map_mul, ha, mul_zero, zero_add, map_one] at h1
  have h2 : aeval a (derivative g) * aeval a q = 1 := by
    rw [← map_mul, mul_comm, map_mul, h1]
  exact isUnit_iff_exists.mpr ⟨aeval a q, h2, h1⟩

/-- Evaluating the reflection of `f` at the inverse of a unit `u`. -/
theorem aeval_inv_reflect_mul_pow (u : Aˣ) (N : ℕ) (f : K[X]) (hf : f.natDegree ≤ N) :
    aeval (↑u⁻¹ : A) (reflect N f) * (u : A) ^ N = aeval (u : A) f := by
  refine induction_with_natDegree_le
    (fun f => aeval (↑u⁻¹ : A) (reflect N f) * (u : A) ^ N = aeval (u : A) f) N ?_ ?_ ?_ f hf
  · simp
  · intro n r _ hnN
    rw [reflect_C_mul_X_pow, revAt_le hnN, map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow,
      aeval_X, aeval_X, mul_assoc]
    congr 1
    have hu : (u⁻¹ ^ (N - n) * u ^ N : Aˣ) = u ^ n := by
      obtain ⟨k, rfl⟩ : ∃ k, N = k + n := ⟨N - n, by omega⟩
      rw [Nat.add_sub_cancel, pow_add, ← mul_assoc, inv_pow, inv_mul_cancel, one_mul]
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val hu
  · intro f g _ _ hf hg
    rw [reflect_add, map_add, add_mul, hf, hg, map_add]

/-- An element annihilated by a polynomial with invertible constant term is a unit. -/
theorem isUnit_of_aeval_eq_zero {K A : Type*} [Field K] [Ring A] [Algebra K A] {g : K[X]}
    (h0 : g.coeff 0 ≠ 0) {a : A} (ha : aeval a g = 0) : IsUnit a := by
  have h := congrArg (aeval a) (divX_mul_X_add g)
  rw [ha, map_add, map_mul, aeval_X, aeval_C] at h
  have h' : aeval a (divX g) * a = -algebraMap K A (g.coeff 0) := eq_neg_of_add_eq_zero_left h
  let w : A := -(g.coeff 0)⁻¹ • aeval a (divX g)
  have hw : w * a = 1 := by
    change (-(g.coeff 0)⁻¹ • aeval a (divX g)) * a = 1
    rw [smul_mul_assoc, h', smul_neg, neg_smul, neg_neg, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ h0, map_one]
  have hc : a * aeval a (divX g) = aeval a (divX g) * a := by
    have := congrArg (aeval a) (mul_comm X (divX g))
    simpa only [map_mul, aeval_X] using this
  have hw' : a * w = 1 := by
    rw [← hw]
    change a * (-(g.coeff 0)⁻¹ • aeval a (divX g)) = (-(g.coeff 0)⁻¹ • aeval a (divX g)) * a
    rw [mul_smul_comm, hc, smul_mul_assoc]
  exact isUnit_iff_exists.mpr ⟨w, hw', hw⟩

end Evaluation

/-- The reverse of a separable polynomial with nonzero constant term is separable. -/
theorem separable_reverse {K : Type*} [Field K] [PerfectField K] {g : K[X]}
    (hg : g.Separable) (h0 : g.coeff 0 ≠ 0) : g.reverse.Separable := by
  rw [PerfectField.separable_iff_squarefree] at hg ⊢
  have hg0 : g ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  have htr : g.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hrr : g.reverse.reverse = g := by
    have hd : g.reverse.natDegree = g.natDegree := by rw [reverse_natDegree, htr, Nat.sub_zero]
    change reflect g.reverse.natDegree g.reverse = g
    rw [hd]
    exact reflect_reflect
  intro d ⟨e, he⟩
  have hl : g.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hg0
  have hd0 : d.coeff 0 ≠ 0 := by
    intro h
    apply hl
    rw [he, mul_coeff_zero, mul_coeff_zero, h, zero_mul, zero_mul]
  have hge : g = d.reverse * d.reverse * e.reverse := by
    rw [← hrr, he, reverse_mul_of_domain, reverse_mul_of_domain]
  have hu : IsUnit d.reverse := hg _ ⟨e.reverse, hge⟩
  have hdt : d.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hd0)
  have hdeg : d.natDegree = 0 := by
    have h := natDegree_eq_zero_of_isUnit hu
    rwa [reverse_natDegree, hdt, Nat.sub_zero] at h
  rw [eq_C_of_natDegree_eq_zero hdeg]
  exact isUnit_C.mpr (IsUnit.mk0 _ hd0)

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- A separable reduced characteristic polynomial of an element of a finite-dimensional
central simple algebra is its minimal polynomial. -/
theorem minpoly_eq_reducedCharpoly_of_separable (a : A)
    (hsep : (reducedCharpoly K A a).Separable) :
    minpoly K a = reducedCharpoly K A a := by
  set p := reducedCharpoly K A a with hp
  set q := minpoly K a with hq
  have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  have hqp : q ∣ p := minpoly.dvd K a (aeval_reducedCharpoly a)
  have hqm : q.Monic := minpoly.monic hint
  have hpm : p.Monic := reducedCharpoly_monic K A a
  suffices hpq : p ∣ q from
    Polynomial.eq_of_monic_of_associated hqm hpm (associated_of_dvd_dvd hqp hpq)
  let Ω := AlgebraicClosure K
  let φ : K →+* Ω := algebraMap K Ω
  let b := Module.finBasis K A
  let M := Algebra.leftMulMatrix b a
  have : Nonempty (Fin (Module.finrank K A)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hchar : M.charpoly = p ^ reducedDegree K A :=
    charpoly_leftMulMatrix_eq_reducedCharpoly_pow K A b a
  have hMq : aeval M q = 0 := by
    change aeval (Algebra.leftMulMatrix b a) q = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  let M' : Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) Ω := M.map φ
  have hM'q : aeval M' (q.map φ) = 0 := by
    have h1 : aeval M' (q.map φ) = (aeval M q).map φ := by
      rw [Polynomial.aeval_map_algebraMap]
      exact Polynomial.aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId K Ω)) M q
    rw [h1, hMq, Matrix.map_zero _ (map_zero φ)]
  have hroots : ∀ x ∈ (p.map φ).roots, x ∈ (q.map φ).roots := by
    intro x hx
    have hp0 : p.map φ ≠ 0 := (hpm.map φ).ne_zero
    have hxroot : (p.map φ).IsRoot x := (mem_roots hp0).1 hx
    have hcharroot : M'.charpoly.IsRoot x := by
      rw [Matrix.charpoly_map, hchar, Polynomial.map_pow]
      rw [Polynomial.IsRoot, eval_pow, hxroot.eq_zero,
        zero_pow (reducedDegree_pos K A).ne']
    have hspec : x ∈ spectrum Ω M' := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hcharroot
    have hmem := spectrum.subset_polynomial_aeval M' (q.map φ) ⟨x, hspec, rfl⟩
    rw [hM'q, spectrum.zero_eq] at hmem
    exact (mem_roots (hqm.map φ).ne_zero).2 hmem
  have hsplit : p.map φ = ((p.map φ).roots.map fun x => X - C x).prod :=
    (IsAlgClosed.splits (p.map φ)).eq_prod_roots_of_monic (hpm.map φ)
  have hnodup : (p.map φ).roots.Nodup := nodup_roots (hsep.map)
  have hle : (p.map φ).roots ≤ (q.map φ).roots :=
    (Multiset.le_iff_subset hnodup).2 hroots
  have hdvd : p.map φ ∣ q.map φ := by
    rw [hsplit]
    exact (Multiset.prod_X_sub_C_dvd_iff_le_roots (hqm.map φ).ne_zero _).2 hle
  exact (Polynomial.map_dvd_map' φ).1 hdvd

/-- If the reduced characteristic polynomial of `a` is separable, the powers
`1, a, …, a^{d-1}` (`d` the reduced degree) are linearly independent. -/
theorem eq_zero_of_sum_smul_pow_eq_zero (a : A) (hsep : (reducedCharpoly K A a).Separable)
    (c : Fin (reducedDegree K A) → K) (hc : ∑ i, c i • a ^ (i : ℕ) = 0) : c = 0 := by
  have hdeg : (minpoly K a).natDegree = reducedDegree K A := by
    rw [minpoly_eq_reducedCharpoly_of_separable a hsep, reducedCharpoly_natDegree]
  have hli := linearIndependent_pow (K := K) a
  rw [hdeg] at hli
  funext i
  exact Fintype.linearIndependent_iff.mp hli c hc i

/-- If the reduced characteristic polynomial of a unit `u` is separable, the powers
`1, u⁻¹, …, u^{-(d-1)}` are linearly independent. -/
theorem eq_zero_of_sum_smul_inv_pow_eq_zero (u : Aˣ)
    (hsep : (reducedCharpoly K A (u : A)).Separable)
    (c : Fin (reducedDegree K A) → K) (hc : ∑ i, c i • (↑u⁻¹ : A) ^ (i : ℕ) = 0) : c = 0 := by
  have hpow (i : Fin (reducedDegree K A)) : (u : A) ^ (reducedDegree K A - 1) *
      (↑u⁻¹ : A) ^ ((Fin.rev i : Fin (reducedDegree K A)) : ℕ) = (u : A) ^ (i : ℕ) := by
    have hu : (u ^ (reducedDegree K A - 1) * u⁻¹ ^ ((Fin.rev i : Fin (reducedDegree K A)) : ℕ) :
        Aˣ) = u ^ (i : ℕ) := by
      have hi : reducedDegree K A - 1 = (i : ℕ) + ((Fin.rev i : Fin (reducedDegree K A)) : ℕ) := by
        rw [Fin.val_rev]
        omega
      rw [hi, pow_add, mul_assoc, inv_pow, mul_inv_cancel, mul_one]
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val hu
  have h : ∑ i, c (Fin.rev i) • (u : A) ^ (i : ℕ) = 0 := by
    have h1 := congrArg (fun y => (u : A) ^ (reducedDegree K A - 1) * y) hc
    simp only [mul_zero, Finset.mul_sum, mul_smul_comm] at h1
    rw [← Equiv.sum_comp Fin.revPerm] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.revPerm_apply, hpow]
  have h2 := eq_zero_of_sum_smul_pow_eq_zero (u : A) hsep _ h
  funext i
  simpa only [Fin.rev_rev, Pi.zero_apply] using congrFun h2 (Fin.rev i)

end Langlands.CentralSimple
