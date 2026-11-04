import Langlands.GroupScheme.Rational.TorusLinearization.Grading

/-! # Descent from a splitting field to the base field -/

noncomputable section

universe u

open MvPolynomial TensorProduct

namespace Langlands.GroupScheme.TorusLinearization

section CoeffMap

variable {k R S : Type*} [CommSemiring k] [CommSemiring R] [CommSemiring S] [Module k R]
  [Module k S] {σ : Type*}

/-- Coefficientwise application of a linear map to a polynomial. -/
def coeffMap (l : R →ₗ[k] S) : MvPolynomial σ R →ₗ[k] MvPolynomial σ S where
  toFun f := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange l l.map_zero f.coeff)
  map_add' f g := by
    refine MvPolynomial.ext _ _ fun m => ?_
    change l ((f + g).coeff m) = l (f.coeff m) + l (g.coeff m)
    rw [show (f + g).coeff m = f.coeff m + g.coeff m by simp, map_add]
  map_smul' c f := by
    refine MvPolynomial.ext _ _ fun m => ?_
    change l ((c • f).coeff m) = c • l (f.coeff m)
    rw [show (c • f).coeff m = c • f.coeff m from rfl, map_smul]

theorem coeff_coeffMap (l : R →ₗ[k] S) (f : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (coeffMap l f).coeff m = l (f.coeff m) := rfl

theorem coeffMap_monomial (l : R →ₗ[k] S) (m : σ →₀ ℕ) (c : R) :
    coeffMap l (monomial m c : MvPolynomial σ R) = monomial m (l c) := by
  classical
  refine MvPolynomial.ext _ _ fun m' => ?_
  rw [coeff_coeffMap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coeffMap_mem_restrictSupport (l : R →ₗ[k] S) {s : Set (σ →₀ ℕ)}
    {f : MvPolynomial σ R} (hf : f ∈ restrictSupport R s) :
    coeffMap l f ∈ restrictSupport S s := by
  rw [mem_restrictSupport_iff] at hf ⊢
  intro m hm
  refine hf ?_
  rw [Finset.mem_coe, mem_support_iff] at hm ⊢
  intro h0
  exact hm (by rw [coeff_coeffMap, h0, map_zero])

end CoeffMap

section Extend

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {σ : Type*}

/-- The `S`-linear extension of an `R`-linear map of polynomials. -/
def extend (ψ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :
    MvPolynomial σ S →ₗ[S] MvPolynomial σ S :=
  (basisMonomials σ S).constr S fun m => MvPolynomial.map (algebraMap R S) (ψ (monomial m 1))

theorem extend_monomial (ψ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) (m : σ →₀ ℕ) (b : S) :
    extend S ψ (monomial m b) = b • MvPolynomial.map (algebraMap R S) (ψ (monomial m 1)) := by
  have h : (monomial m b : MvPolynomial σ S) = b • basisMonomials σ S m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, extend, Module.Basis.constr_basis]

theorem map_smul_eq (r : R) (g : MvPolynomial σ R) :
    MvPolynomial.map (algebraMap R S) (r • g) = algebraMap R S r • MvPolynomial.map (algebraMap R S) g := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

theorem extend_map (ψ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) (g : MvPolynomial σ R) :
    extend S ψ (MvPolynomial.map (algebraMap R S) g) =
      MvPolynomial.map (algebraMap R S) (ψ g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial m r =>
    have h : (monomial m r : MvPolynomial σ R) = r • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [map_monomial, extend_monomial, h, map_smul, map_smul_eq]
  | add g h hg hh => rw [map_add, map_add, hg, hh, map_add, map_add]

end Extend

section Theta

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- A `k`-linear form on `K` with value `1` at `1`. -/
theorem exists_theta : ∃ θ : K →ₗ[k] k, θ 1 = 1 := by
  obtain ⟨g, hg⟩ := (Algebra.linearMap k K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective)
  refine ⟨g, ?_⟩
  have := LinearMap.congr_fun hg 1
  simpa using this

end Theta

section Tensor

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (B : Type u) [CommRing B] [Algebra k B]

/-- The extension `K ⊗ B → B` of a `k`-linear form on `K`. -/
def tens (l : K →ₗ[k] k) : K ⊗[k] B →ₗ[k] B :=
  (TensorProduct.lid k B).toLinearMap ∘ₗ TensorProduct.map l LinearMap.id

theorem tens_tmul (l : K →ₗ[k] k) (c : K) (b : B) : tens B l (c ⊗ₜ b) = l c • b := by
  simp [tens]

end Tensor

namespace PointAction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {I : Type u} {n : ℕ}
  (a : PointAction k K I n)

/-- The extension of a point to `K ⊗ B`. -/
abbrev ext {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B) : a.Pt (K ⊗[k] B) :=
  a.map Algebra.TensorProduct.includeRight t

/-- Linear forms on `K` commute with the action, through the extension to `K ⊗ B`. -/
theorem pull_coeffMap (l : K →ₗ[k] k) {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B)
    (h : MvPolynomial (Fin n) K) :
    a.pull t (coeffMap l h) = coeffMap (tens B l) (a.pullK (a.ext t) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial m c =>
    have hp : a.poly (a.ext t) = fun i =>
        MvPolynomial.map (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom
          (a.poly t i) := funext fun i => a.poly_map _ t i
    set P := m.prod fun i e => a.poly t i ^ e
    have hP : (m.prod fun i e => (a.poly (a.ext t) i) ^ e) =
        MvPolynomial.map (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom P := by
      rw [hp, map_finsuppProd]
      simp only [map_pow]
    rw [coeffMap_monomial, pull, pullK, aeval_monomial, aeval_monomial, hP]
    refine MvPolynomial.ext _ _ fun m' => ?_
    rw [coeff_coeffMap, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, coeff_C_mul,
      coeff_C_mul, coeff_map]
    have h1 : algebraMap K (K ⊗[k] B) c = c ⊗ₜ 1 := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, tens_tmul, Algebra.smul_def]
  | add g h hg hh => rw [map_add, map_add, hg, hh, map_add, map_add]

end PointAction

end Langlands.GroupScheme.TorusLinearization
