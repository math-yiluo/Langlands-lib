import Langlands.CommutativeAlgebra.Popescu.FaltingsPIndependence

/-! # The presentation `R[x₁, …, x_n]/(x_j^p − a_j)` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open MvPolynomial

/-- The ideal `(x_j^p − a_j)` of `R[x₁, …, x_n]`. -/
noncomputable abbrev rootIdeal {R : Type*} [CommRing R] (p : ℕ) {n : ℕ} (a : Fin n → R) :
    Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun j => X j ^ p - C (a j))

/-- The monomial `∏ x_j^{r_j}` for `r : Fin n → Fin p`. -/
noncomputable abbrev redMonomial {R : Type*} [CommRing R] {p n : ℕ} (r : Fin n → Fin p) :
    MvPolynomial (Fin n) R :=
  ∏ j, X j ^ (r j : ℕ)

theorem quot_C_mul {R : Type*} [CommRing R] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R)) (c : R)
    (g : MvPolynomial (Fin n) R) :
    Ideal.Quotient.mk I (C c * g) = c • Ideal.Quotient.mk I g := by
  rw [← smul_eq_C_mul]
  exact map_smul (Ideal.Quotient.mkₐ R I) c g

theorem redMonomial_mul_X {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
    (a : Fin n → R) (r : Fin n → Fin p) (j : Fin n) :
    Ideal.Quotient.mk (rootIdeal p a) (redMonomial r * X j) ∈
      Submodule.span R (Set.range fun r : Fin n → Fin p =>
        Ideal.Quotient.mk (rootIdeal p a) (redMonomial r)) := by
  classical
  have hsplit : ∀ s : Fin n → Fin p, (redMonomial s : MvPolynomial (Fin n) R) =
      X j ^ (s j : ℕ) * ∏ i ∈ Finset.univ.erase j, X i ^ (s i : ℕ) :=
    fun s => (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  by_cases hlt : (r j : ℕ) + 1 < p
  · obtain ⟨r', hr'j, hr'i⟩ : ∃ r' : Fin n → Fin p, r' j = ⟨r j + 1, hlt⟩ ∧
        ∀ i, i ≠ j → r' i = r i :=
      ⟨Function.update r j ⟨r j + 1, hlt⟩, Function.update_self _ _ _,
        fun i hi => Function.update_of_ne hi _ _⟩
    have hr' : redMonomial r * X j = (redMonomial r' : MvPolynomial (Fin n) R) := by
      rw [hsplit r, hsplit r']
      have hrest : ∏ i ∈ Finset.univ.erase j, X i ^ (r' i : ℕ) =
          ∏ i ∈ Finset.univ.erase j, (X i ^ (r i : ℕ) : MvPolynomial (Fin n) R) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [hr'i i (Finset.ne_of_mem_erase hi)]
      rw [hrest, hr'j, pow_succ]
      ring
    rw [hr']
    exact Submodule.subset_span ⟨r', rfl⟩
  · have heq : (r j : ℕ) + 1 = p := le_antisymm (r j).isLt (not_lt.mp hlt)
    obtain ⟨r', hr'j, hr'i⟩ : ∃ r' : Fin n → Fin p, r' j = ⟨0, hp.out.pos⟩ ∧
        ∀ i, i ≠ j → r' i = r i :=
      ⟨Function.update r j ⟨0, hp.out.pos⟩, Function.update_self _ _ _,
        fun i hi => Function.update_of_ne hi _ _⟩
    have hr' : redMonomial r * X j =
        (redMonomial r' * X j ^ p : MvPolynomial (Fin n) R) := by
      rw [hsplit r, hsplit r']
      have hrest : ∏ i ∈ Finset.univ.erase j, X i ^ (r' i : ℕ) =
          ∏ i ∈ Finset.univ.erase j, (X i ^ (r i : ℕ) : MvPolynomial (Fin n) R) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [hr'i i (Finset.ne_of_mem_erase hi)]
      rw [hrest, hr'j, congrArg (fun m => (X j : MvPolynomial (Fin n) R) ^ m) heq.symm]
      simp only [pow_zero, one_mul, pow_succ]
      ring
    have hmod : Ideal.Quotient.mk (rootIdeal p a) (X j ^ p) =
        Ideal.Quotient.mk (rootIdeal p a) (C (a j)) := by
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨j, rfl⟩
    rw [hr', map_mul, hmod, ← map_mul, mul_comm, quot_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r', rfl⟩)

/-- `R[x]/(x_j^p − a_j)` is spanned by the reduced monomials. -/
theorem span_redMonomial {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
    (a : Fin n → R) :
    Submodule.span R (Set.range fun r : Fin n → Fin p =>
      Ideal.Quotient.mk (rootIdeal p a) (redMonomial r)) = ⊤ := by
  classical
  set S := Submodule.span R (Set.range fun r : Fin n → Fin p =>
    Ideal.Quotient.mk (rootIdeal p a) (redMonomial r))
  have hmulX : ∀ s ∈ S, ∀ j, s * Ideal.Quotient.mk (rootIdeal p a) (X j) ∈ S := by
    intro s hs j
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      rw [← map_mul]
      exact redMonomial_mul_X p a r j
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  rintro y -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction f using MvPolynomial.induction_on with
  | C c =>
    have h1 : Ideal.Quotient.mk (rootIdeal p a) (C c) =
        c • Ideal.Quotient.mk (rootIdeal p a) (redMonomial (fun _ => ⟨0, hp.out.pos⟩)) := by
      rw [← quot_C_mul]
      simp
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | mul_X f j hf => rw [map_mul]; exact hmulX _ hf j

/-- `dim_k k[x]/(x_j^p − a_j) ≤ p^n`. -/
theorem finrank_rootQuot_le {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] {n : ℕ}
    (a : Fin n → k) :
    FiniteDimensional k (MvPolynomial (Fin n) k ⧸ rootIdeal p a) ∧
      Module.finrank k (MvPolynomial (Fin n) k ⧸ rootIdeal p a) ≤ p ^ n := by
  classical
  have hspan := span_redMonomial (R := k) p a
  have hfin : FiniteDimensional k (MvPolynomial (Fin n) k ⧸ rootIdeal p a) := by
    refine ⟨?_⟩
    rw [← hspan]
    exact Submodule.fg_span (Set.finite_range _)
  refine ⟨hfin, ?_⟩
  rw [← finrank_top, ← hspan]
  refine (finrank_range_le_card _).trans ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- If `L = k(β)` with `β_j^p = a_j` and the `da_j` independent, the kernel of `k[x] → L`,
`x_j ↦ β_j`, is exactly `(x_j^p − a_j)`. -/
theorem ker_aeval_eq_rootIdeal (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {n : ℕ}
    (a : Fin n → k) (hind : LinearIndependent k fun j => KaehlerDifferential.D ℤ k (a j))
    {L : Type u} [Field L] [Algebra k L] (β : Fin n → L)
    (hgen : Algebra.adjoin k (Set.range β) = ⊤) (hβ : ∀ j, β j ^ p = algebraMap k L (a j)) :
    RingHom.ker (aeval β : MvPolynomial (Fin n) k →ₐ[k] L) = rootIdeal p a := by
  have hle : rootIdeal p a ≤ RingHom.ker (aeval β : MvPolynomial (Fin n) k →ₐ[k] L) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, aeval_X, aeval_C, hβ, sub_self]
  let ψ : (MvPolynomial (Fin n) k ⧸ rootIdeal p a) →ₐ[k] L :=
    Ideal.Quotient.liftₐ (rootIdeal p a) (aeval β) (fun x hx => hle hx)
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (aeval β : MvPolynomial (Fin n) k →ₐ[k] L).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]
      exact Algebra.mem_top
    obtain ⟨f, rfl⟩ := hy
    exact ⟨Ideal.Quotient.mk _ f, rfl⟩
  obtain ⟨hfin, hdim⟩ := finrank_rootQuot_le (k := k) p a
  have hL := finrank_pRoots p n a hind L β hgen hβ
  have hinj : Function.Injective ψ := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ.toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hL] at hrn
    have hker : Module.finrank k (LinearMap.ker ψ.toLinearMap) = 0 := by omega
    have : LinearMap.ker ψ.toLinearMap = ⊥ := Submodule.finrank_eq_zero.mp hker
    exact LinearMap.ker_eq_bot.mp this
  apply le_antisymm _ hle
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact hx

end Faltings

end Langlands.CommutativeAlgebra.Popescu
