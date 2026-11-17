import Langlands.Representation.Archimedean.ComplexGelfandSeparation
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.ComplexStandardJacquetExponentRoute

/-!
# Casselman–Osborne for complex principal series

Proof of `ComplexJacquetCasselmanOsborneStatement`. Gelfand's central elements
`tr (E^{(i)})^k` of the two factors of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` act on `X(d)` by scalars `c_{i,k}`.
Modulo `𝔫X(d)` they act as Gelfand's polynomials in the diagonal generators
(`ComplexJacquetFinite.diag_pow`), so every nonzero Jacquet functional with holomorphic and
antiholomorphic coordinates `P`, `Q` satisfies `∑_a g_k(a)(P) = c_{0,k}` and
`∑_a g_k(a)(Q) = c_{1,k}`. Evaluation at `1` is such a functional with `P = p(d) + ρ`,
`Q = q(d) + ρ`, and Gelfand's polynomials separate shifted diagonals up to permutation
(`GelfandSeparation.exists_perm_of_gel_eq`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace JacquetCasselmanOsborne

open ComplexJacquetFinite ComplexGenericLarge GelfandSeparation MvPolynomial

section Abstract

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- Gelfand's elements act by scalars when the product action has an infinitesimal character
(as `ComplexJacquetFinite.trace_scalar`, with the infinitesimal character as hypothesis). -/
theorem trace_scalar_of_inf (hinf : HasInfinitesimalCharacter (prodAction π)) (i : Fin 2)
    (k : ℕ) : ∃ c : ℂ, ∀ v, ∑ p, (Matrix.of (ee π i) ^ k) p p v = c • v := by
  obtain ⟨c, hc⟩ := hinf _ (Kostant.gel_mem_center ℂ (fun _ : Fin 2 => n) i k)
  refine ⟨c, fun v => ?_⟩
  have h := LinearMap.congr_fun hc v
  rw [Kostant.gel, map_sum, LinearMap.sum_apply] at h
  simp only [envelopingAction_pw] at h
  rw [h, Module.algebraMap_end_apply]

/-- The side relation `∑_a g_k(a) - c` acts into `𝔫V` (as `ComplexJacquetFinite.side_rel`,
with the infinitesimal character as hypothesis). -/
theorem side_rel_of_inf (hinf : HasInfinitesimalCharacter (prodAction π)) (i : Fin 2) (k : ℕ) :
    ∃ c : ℂ, rename (fun a : Fin n => (i, a)) (∑ a, gelPoly n k a - C c) ∈ annIdeal π := by
  obtain ⟨c, hc⟩ := trace_scalar_of_inf π hinf i k
  refine ⟨c, fun v => ?_⟩
  set ψ := (diagAct π).comp (rename (R := ℂ) fun a : Fin n => (i, a)) with hψdef
  have hψ : ∀ a, ψ (X a) = ee π i a a := by
    intro a
    simp [hψdef, diagAct_X, diagGen]
  have hsum := Submodule.sum_mem (complexJacquetSubspace n π) (t := Finset.univ) fun a _ =>
    diag_pow (complexJacquetSubspace n π) (isGlFamily_ee π i) (ee_up π i) (ee_diag π i) ψ hψ
      k a v
  rw [Finset.sum_sub_distrib, hc] at hsum
  have heq : diagAct π (rename (fun a : Fin n => (i, a)) (∑ a, gelPoly n k a - C c)) v =
      -(c • v - ∑ a, ψ (gelPoly n k a) v) := by
    have : diagAct π (rename (fun a : Fin n => (i, a)) (∑ a, gelPoly n k a - C c)) =
        ψ (∑ a, gelPoly n k a - C c) := rfl
    rw [this, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, MvPolynomial.algHom_C,
      Module.algebraMap_end_apply, neg_sub]
  rw [heq]
  exact Submodule.neg_mem _ hsum

/-- The holomorphic (`s.1 = 0`) and antiholomorphic (`s.1 = 1`) coordinates
`P_j = (a_j - i b_j)/2`, `Q_j = (a_j + i b_j)/2` of the exponents. -/
def PQ (a b : Fin n → ℂ) (s : Fin 2 × Fin n) : ℂ :=
  if s.1 = 0 then (a s.2 - Complex.I * b s.2) / 2 else (a s.2 + Complex.I * b s.2) / 2

variable {π}

theorem jacquet_kills {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ}
    (hJ : IsComplexJacquetFunctional n π ℓ a b) :
    ∀ w ∈ complexJacquetSubspace n π, ℓ w = 0 := by
  have h : complexJacquetSubspace n π ≤ LinearMap.ker ℓ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨X, v, hX, rfl⟩
    exact hJ.1 X hX v
  exact fun w hw => h hw

theorem conjMat_single_one (j : Fin n) :
    conjMat (Matrix.single j j (1 : ℂ)) = Matrix.single j j 1 := by
  ext p q
  simp only [conjMat_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem I_smul_single_one (j : Fin n) :
    Complex.I • Matrix.single j j (1 : ℂ) = Matrix.single j j Complex.I := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem jacquet_ee {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ}
    (hJ : IsComplexJacquetFunctional n π ℓ a b) (i : Fin 2) (j : Fin n) (v : V) :
    ℓ (ee π i j j v) = PQ a b (i, j) * ℓ v := by
  rw [ee, prodAction_apply_eq]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  fin_cases i
  · have hY0 : unitPair (0 : Fin 2) j j 0 = Matrix.single j j (1 : ℂ) := Pi.single_eq_same _ _
    have hY1 : unitPair (0 : Fin 2) j j 1 = 0 := Pi.single_eq_of_ne h10 _
    simp only [Fin.zero_eta] at *
    rw [hY0, hY1]
    simp only [conjMat, Matrix.map_zero, smul_zero, TensorProduct.tmul_zero, map_zero,
      LinearMap.zero_apply, add_zero, I_smul_single_one]
    rw [map_smul, map_sub, map_smul, (hJ.2 j v).1, (hJ.2 j v).2]
    simp only [PQ, ite_true, smul_eq_mul]
    ring
  · have hY0 : unitPair (1 : Fin 2) j j 0 = 0 := Pi.single_eq_of_ne h10.symm _
    have hY1 : unitPair (1 : Fin 2) j j 1 = Matrix.single j j (1 : ℂ) := Pi.single_eq_same _ _
    simp only [Fin.mk_one] at *
    rw [hY0, hY1]
    simp only [smul_zero, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply, sub_zero,
      zero_add, conjMat_single_one, I_smul_single_one]
    rw [map_smul, map_add, map_smul, (hJ.2 j v).1, (hJ.2 j v).2]
    simp only [PQ, h10, ite_false, smul_eq_mul]
    ring

/-- A Jacquet functional turns the diagonal action into evaluation at `(P, Q)`. -/
theorem jacquet_diagAct {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ}
    (hJ : IsComplexJacquetFunctional n π ℓ a b) (f : MvPolynomial (Fin 2 × Fin n) ℂ) :
    ∀ v, ℓ (diagAct π f v) = eval (PQ a b) f * ℓ v := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    intro v
    rw [MvPolynomial.algHom_C, Module.algebraMap_end_apply, map_smul, eval_C, smul_eq_mul]
  | add p q hp hq =>
    intro v
    rw [map_add, LinearMap.add_apply, map_add, hp, hq, map_add, add_mul]
  | mul_X p s hp =>
    intro v
    rw [map_mul, Module.End.mul_apply, hp, diagAct_X, diagGen, jacquet_ee hJ, eval_mul, eval_X]
    ring

/-- Two nonzero Jacquet functionals have the same Gelfand sums in each factor. -/
theorem gel_sum_eq (hinf : HasInfinitesimalCharacter (prodAction π))
    {ℓ ℓ' : V →ₗ[ℂ] ℂ} {a b a' b' : Fin n → ℂ} (hℓ : ℓ ≠ 0)
    (hJ : IsComplexJacquetFunctional n π ℓ a b) (hℓ' : ℓ' ≠ 0)
    (hJ' : IsComplexJacquetFunctional n π ℓ' a' b') (i : Fin 2) (k : ℕ) :
    ∑ c, gv (fun j => PQ a b (i, j)) k c = ∑ c, gv (fun j => PQ a' b' (i, j)) k c := by
  obtain ⟨c, hc⟩ := side_rel_of_inf π hinf i k
  have key : ∀ (m : V →ₗ[ℂ] ℂ) (a b : Fin n → ℂ), m ≠ 0 →
      IsComplexJacquetFunctional n π m a b → ∑ x, gv (fun j => PQ a b (i, j)) k x = c := by
    intro m a b hm hJm
    obtain ⟨v, hv⟩ : ∃ v, m v ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (LinearMap.ext h)
    have h0 := jacquet_kills hJm _ (hc v)
    rw [jacquet_diagAct hJm, MvPolynomial.eval_rename, map_sub, map_sum, eval_C] at h0
    have h1 : (∑ x, eval (PQ a b ∘ fun a : Fin n => (i, a)) (gelPoly n k x) - c) = 0 :=
      (mul_eq_zero.1 h0).resolve_right hv
    exact sub_eq_zero.1 h1
  rw [key ℓ a b hℓ hJ, key ℓ' a' b' hℓ' hJ']

end Abstract

end JacquetCasselmanOsborne

open LocalFactor.Archimedean JacquetCasselmanOsborne GelfandSeparation ComplexGenericLarge

/-- **Casselman–Osborne for complex principal series.** -/
theorem complexJacquetCasselmanOsborne : ComplexJacquetCasselmanOsborneStatement := by
  intro n d ℓ a b hℓ hJ
  have hn : (List.ofFn d).length = n := List.length_ofFn
  have hinf : HasInfinitesimalCharacter (prodAction (complexStandardLie n (List.ofFn d))) :=
    Kostant.hasInfinitesimalCharacter_comp tensorLieEquiv
      (complexStandardLie_hasInfinitesimalCharacter n _)
  -- evaluation at `1`
  have hJev := ComplexTemperedComplement.isComplexJacquetFunctional_eval_comp hn LinearMap.id
    (fun _ _ => rfl)
  have hev : kFiniteEval (complexStandardModule n (List.ofFn d)) 1 ∘ₗ LinearMap.id ≠ 0 := by
    intro h0
    apply hℓ
    ext f
    have hf : f = 0 := ComplexPermutation.kFiniteEval_one_separating (List.ofFn d) f (fun k => by
      have := LinearMap.congr_fun h0 (complexStandardRep n (List.ofFn d) k f)
      simpa using this)
    rw [hf, map_zero, LinearMap.zero_apply]
  have hk1 : ∀ j : Fin n, ComplexSwapJacquet.kappa (List.ofFn d) hn j 1 =
      2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) := by
    intro j
    simp [ComplexSwapJacquet.kappa]
  have hkI : ∀ j : Fin n, ComplexSwapJacquet.kappa (List.ofFn d) hn j Complex.I =
      Complex.I * ((d j).weight : ℂ) := by
    intro j
    simp [ComplexSwapJacquet.kappa]
  obtain ⟨α, hα⟩ := exists_perm_of_gel_eq _ _ (gel_sum_eq hinf hℓ hJ hev hJev 0)
  obtain ⟨β, hβ⟩ := exists_perm_of_gel_eq _ _ (gel_sum_eq hinf hℓ hJ hev hJev 1)
  refine ⟨α, β, fun j => ?_⟩
  have h0 := hα j
  have h1 := hβ j
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [PQ, ite_true, h10, ite_false, hk1, hkI] at h0 h1
  constructor
  · linear_combination h0 + h1 +
      ((((d (β j)).weight : ℂ) - ((d (α j)).weight : ℂ)) / 2) * Complex.I_sq
  · linear_combination Complex.I * (h0 - h1) +
      (b j - Complex.I * (((d (α j)).weight : ℂ) + ((d (β j)).weight : ℂ)) / 2) * Complex.I_sq

end Langlands.Archimedean
