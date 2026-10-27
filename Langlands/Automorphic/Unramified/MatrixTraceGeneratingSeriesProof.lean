import Langlands.Automorphic.Unramified.PolynomialTraceGeneratingSeriesProof
import Langlands.Automorphic.Unramified.TraceGeneratingSeriesStatement
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
Proof of `MatrixTraceGeneratingSeriesStatement`: the positive coefficients of
the trace series of the reversed characteristic polynomial of a complex square
matrix are the traces of its powers.
-/

open scoped BigOperators
open Polynomial

namespace Langlands.Automorphic.Unramified

/-- The trace series of a linear factor `1 - r X` has `k`-th coefficient `r ^ k`
for every positive `k`. -/
theorem coeff_polynomialTraceSeries_one_sub_C_mul_X (r : ℂ) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k (polynomialTraceSeries (1 - C r * X)) = r ^ k := by
  have hcoe : ((1 - C r * X : ℂ[X]) : PowerSeries ℂ) =
      1 - PowerSeries.C r * PowerSeries.X := by
    simp
  have hder : PowerSeries.derivative ((1 - C r * X : ℂ[X]) : PowerSeries ℂ) =
      -PowerSeries.C r := by
    rw [PowerSeries.derivative_coe]
    simp
  have hinv : ((1 - C r * X : ℂ[X]) : PowerSeries ℂ)⁻¹ = PowerSeries.mk fun n => r ^ n := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp), hcoe]
    ext n
    rcases n with _ | n
    · simp
    · rw [mul_comm, sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
      simp [pow_succ']
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hseries : polynomialTraceSeries (1 - C r * X) =
      PowerSeries.X * (PowerSeries.C r * PowerSeries.mk fun n => r ^ n) := by
    rw [polynomialTraceSeries, hder, hinv]
    ring
  rw [hseries, zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk, pow_succ']

/-- Trace-series additivity over a finite multiset of normalized polynomials. -/
theorem polynomialTraceSeries_multiset_prod (s : Multiset ℂ[X])
    (hs : ∀ P ∈ s, P.coeff 0 = 1) :
    polynomialTraceSeries s.prod = (s.map polynomialTraceSeries).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    have hP : P.coeff 0 = 1 := hs P (Multiset.mem_cons_self P s)
    have hs' : ∀ Q ∈ s, Q.coeff 0 = 1 := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
    have hprod : s.prod.coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_multiset_prod]
      exact Multiset.prod_eq_one fun c hc => by
        obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hc
        exact hs' Q hQ
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      polynomialTraceSeries_mul P s.prod hP hprod, ih hs']

/-- The reversed characteristic polynomial of a complex matrix is the product of
the linear factors `1 - r X` over the roots `r` of its characteristic polynomial,
counted with multiplicity. -/
theorem charpolyRev_eq_prod_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.charpolyRev = (A.charpoly.roots.map fun r => 1 - C r * X).prod := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by
    simpa using reverse_C (1 : ℂ)
  have hlin : ∀ a : ℂ, (X - C a : ℂ[X]).reverse = 1 - C a * X := by
    intro a
    have hX : (X : ℂ[X]).reverse = 1 := by
      simpa [h1] using reverse_X_mul (1 : ℂ[X])
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, pow_one, hX, C_neg, neg_mul,
      ← sub_eq_add_neg]
  rw [← Matrix.reverse_charpoly]
  conv_lhs =>
    rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic A)]
  generalize A.charpoly.roots = s
  induction s using Multiset.induction_on with
  | empty => simpa using h1
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, hlin,
      Multiset.map_cons, Multiset.prod_cons]

/-- On a finite-dimensional space, if `g - μ` is nilpotent then the trace of
`g ^ k` is `μ ^ k` times the dimension. -/
theorem trace_pow_eq_of_isNilpotent_sub {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] {g : Module.End ℂ V} {μ : ℂ}
    (hg : IsNilpotent (g - algebraMap ℂ (Module.End ℂ V) μ)) (k : ℕ) :
    LinearMap.trace ℂ V (g ^ k) = μ ^ k * Module.finrank ℂ V := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ ((Commute.refl g).pow_left k) hg,
      ih, pow_succ]
    ring

/-- The trace of a power of a complex matrix is the corresponding power sum of
the roots of its characteristic polynomial, counted with multiplicity. -/
theorem trace_pow_eq_sum_roots_charpoly_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix.trace (A ^ k) = (A.charpoly.roots.map fun r => r ^ k).sum := by
  classical
  let f : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have htr : Matrix.trace (A ^ k) = LinearMap.trace ℂ _ (f ^ k) := by
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow]
  have hds : DirectSum.IsInternal fun μ => f.maxGenEigenspace μ :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.independent_maxGenEigenspace
      (Module.End.iSup_maxGenEigenspace_eq_top f)
  have hfin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hmaps : ∀ μ, Set.MapsTo (f ^ k) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right k) μ
  have hloc : ∀ μ, LinearMap.trace ℂ (f.maxGenEigenspace μ) ((f ^ k).restrict (hmaps μ)) =
      (A.charpoly.rootMultiplicity μ : ℂ) * μ ^ k := by
    intro μ
    have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
      f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
    have hnil : IsNilpotent (f.restrict h1 -
        algebraMap ℂ (Module.End ℂ (f.maxGenEigenspace μ)) μ) :=
      f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have hpow : (f ^ k).restrict (hmaps μ) = (f.restrict h1) ^ k :=
      (Module.End.pow_restrict k h1).symm
    rw [hpow, trace_pow_eq_of_isNilpotent_sub hnil, LinearMap.finrank_maxGenEigenspace_eq, hcp,
      mul_comm]
  have hset : hfin.toFinset = A.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset, ← Multiset.count_pos,
      Polynomial.count_roots, ← hcp, ← LinearMap.finrank_maxGenEigenspace_eq, Ne,
      ← Submodule.finrank_eq_zero, pos_iff_ne_zero]
  rw [htr, LinearMap.trace_eq_sum_trace_restrict' hds hfin hmaps, Finset.sum_multiset_map_count,
    hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hloc μ, Polynomial.count_roots, nsmul_eq_mul]

/-- The complete published matrix trace generating series proposition. -/
theorem matrixTraceGeneratingSeries : MatrixTraceGeneratingSeriesStatement := by
  intro n A k hk
  have hfac : ∀ P ∈ A.charpoly.roots.map (fun r => 1 - C r * X), P.coeff 0 = 1 := by
    intro P hP
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hP
    simp
  rw [charpolyRev_eq_prod_roots, polynomialTraceSeries_multiset_prod _ hfac, map_multiset_sum,
    Multiset.map_map, Multiset.map_map, trace_pow_eq_sum_roots_charpoly_pow]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  exact coeff_polynomialTraceSeries_one_sub_C_mul_X r hk

end Langlands.Automorphic.Unramified
