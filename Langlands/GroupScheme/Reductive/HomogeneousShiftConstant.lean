import Mathlib

/-! # A homogeneous polynomial constant along an affine line forces a constant parameter -/

open MvPolynomial

namespace Langlands.GroupScheme.HomogeneousShift

variable {K : Type*} [Field K] {σ : Type*}

/-- Evaluation of a homogeneous polynomial of degree `d` scales by the `d`-th power. -/
theorem aeval_smul_of_isHomogeneous {S : Type*} [CommRing S] [Algebra K S]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d) (t : S) (x : σ → S) :
    aeval (t • x) F = t ^ d * aeval x F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg := hF (mem_support_iff.mp hα)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finsupp.prod_mul]
  have ht : (α.prod fun _ k => t ^ k) = t ^ d := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← hdeg, Finsupp.weight_apply, Finsupp.sum]
    simp
  rw [ht]
  ring

/-- An element of a domain that is integral over an algebraically closed field is a scalar. -/
theorem mem_range_of_isIntegral [IsAlgClosed K] {C : Type*} [CommRing C] [IsDomain C]
    [Algebra K C] {x : C} (hx : IsIntegral K x) : x ∈ Set.range (algebraMap K C) := by
  have h : (minpoly K x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx)
  have hq : (minpoly K x).leadingCoeff = 1 := minpoly.monic hx
  have : Polynomial.aeval x (minpoly K x) = 0 := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at this
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact this.symm⟩

/-- If a homogeneous polynomial of positive degree, not vanishing at `a`, is constant along the
line `w + ψ • a` with parameter `ψ` in a domain over an algebraically closed field, then `ψ` is a
scalar. -/
theorem mem_range_of_aeval_shift [IsAlgClosed K] {C : Type*} [CommRing C] [IsDomain C]
    [Algebra K C] {F : MvPolynomial σ K} {d : ℕ} (hd : 0 < d) (hF : F.IsHomogeneous d)
    (w a : σ → K) (ha : eval a F ≠ 0) (ψ : C) (c : K)
    (h : aeval (fun j => algebraMap K C (w j) + algebraMap K C (a j) * ψ) F =
      algebraMap K C c) :
    ψ ∈ Set.range (algebraMap K C) := by
  classical
  let r : Polynomial K :=
    aeval (fun j => Polynomial.C (w j) + Polynomial.C (a j) * Polynomial.X) F - Polynomial.C c
  have hr : Polynomial.aeval ψ r = 0 := by
    have hc := MvPolynomial.comp_aeval (R := K)
      (fun j => Polynomial.C (w j) + Polynomial.C (a j) * Polynomial.X)
      (Polynomial.aeval (R := K) ψ)
    have hc' := congrArg (fun φ : MvPolynomial σ K →ₐ[K] C => φ F) hc
    simp only [AlgHom.comp_apply] at hc'
    simp only [r, map_sub, hc', Polynomial.aeval_C, map_add, map_mul, Polynomial.aeval_X, h,
      sub_self]
  -- the reversed polynomial vanishes at every nonzero scalar
  let p : Polynomial K :=
    aeval (fun j => Polynomial.C (w j) * Polynomial.X + Polynomial.C (a j)) F -
      Polynomial.C c * Polynomial.X ^ d
  have hp0 : p.eval 0 = eval a F := by
    have hc := MvPolynomial.comp_aeval (R := K)
      (fun j => Polynomial.C (w j) * Polynomial.X + Polynomial.C (a j))
      (Polynomial.aeval (R := K) (0 : K))
    have hc' := congrArg (fun φ : MvPolynomial σ K →ₐ[K] K => φ F) hc
    simp only [AlgHom.comp_apply] at hc'
    rw [← Polynomial.coe_aeval_eq_eval, map_sub, hc']
    simp [hd.ne']
  have hr0 : r ≠ 0 := by
    intro hr0
    have hroot : ∀ t : K, t ≠ 0 → p.IsRoot t := by
      intro t ht
      have hrt : r.eval t⁻¹ = 0 := by rw [hr0, Polynomial.eval_zero]
      have hc := MvPolynomial.comp_aeval (R := K)
        (fun j => Polynomial.C (w j) + Polynomial.C (a j) * Polynomial.X)
        (Polynomial.aeval (R := K) t⁻¹)
      have hc' := congrArg (fun φ : MvPolynomial σ K →ₐ[K] K => φ F) hc
      simp only [AlgHom.comp_apply] at hc'
      have hc2 := MvPolynomial.comp_aeval (R := K)
        (fun j => Polynomial.C (w j) * Polynomial.X + Polynomial.C (a j))
        (Polynomial.aeval (R := K) t)
      have hc2' := congrArg (fun φ : MvPolynomial σ K →ₐ[K] K => φ F) hc2
      simp only [AlgHom.comp_apply] at hc2'
      rw [← Polynomial.coe_aeval_eq_eval, map_sub, hc'] at hrt
      simp only [Polynomial.aeval_C, map_add, map_mul, Polynomial.aeval_X, Algebra.algebraMap_self,
        RingHom.id_apply] at hrt
      rw [Polynomial.IsRoot, ← Polynomial.coe_aeval_eq_eval, map_sub, hc2']
      simp only [Polynomial.aeval_C, map_add, map_mul, Polynomial.aeval_X, map_pow,
        Algebra.algebraMap_self, RingHom.id_apply]
      have hscale : (fun j => w j * t + a j) = t • fun j => w j + a j * t⁻¹ := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [hscale, aeval_smul_of_isHomogeneous hF, sub_eq_zero.mp hrt]
      ring
    have hinf : {t : K | p.IsRoot t}.Infinite :=
      (Set.infinite_univ.sdiff (Set.finite_singleton 0)).mono fun t ht => hroot t ht.2
    have hp := Polynomial.eq_zero_of_infinite_isRoot p hinf
    exact ha (by rw [← hp0, hp, Polynomial.eval_zero])
  exact mem_range_of_isIntegral (IsAlgebraic.isIntegral ⟨r, hr0, hr⟩)

end Langlands.GroupScheme.HomogeneousShift
