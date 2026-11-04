import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Linear spanning by polynomial nonvanishing -/

noncomputable section

universe u v w

open Module

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    {ι : Type w} [Fintype ι]

/-- The polynomial of a linear functional in the coordinates of a finite basis. -/
def basisLinearFormPolynomial (b : Basis ι k V) (ℓ : V →ₗ[k] k) :
    MvPolynomial ι k :=
  ∑ i, MvPolynomial.C (ℓ (b i)) * MvPolynomial.X i

@[simp]
theorem eval_basisLinearFormPolynomial (b : Basis ι k V) (ℓ : V →ₗ[k] k)
    (x : V) :
    MvPolynomial.eval (b.repr x) (basisLinearFormPolynomial b ℓ) = ℓ x := by
  classical
  calc
    MvPolynomial.eval (b.repr x) (basisLinearFormPolynomial b ℓ) =
        ∑ i, b.repr x i * ℓ (b i) := by
      simp [basisLinearFormPolynomial, mul_comm]
    _ = ℓ (∑ i, b.repr x i • b i) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = ℓ x := by rw [b.sum_repr]

@[simp]
theorem basisLinearFormPolynomial_eq_zero_iff (b : Basis ι k V) (ℓ : V →ₗ[k] k) :
    basisLinearFormPolynomial b ℓ = 0 ↔ ℓ = 0 := by
  constructor
  · intro h
    ext x
    have he := eval_basisLinearFormPolynomial b ℓ x
    rw [h, map_zero] at he
    exact he.symm
  · rintro rfl
    simp [basisLinearFormPolynomial]

/-- A subspace containing the nonvanishing locus of a nonzero polynomial
in finite basis coordinates is the entire vector space over an infinite field. -/
theorem submodule_eq_top_of_polynomial_nonvanishing [Infinite k]
    (b : Basis ι k V) {p : MvPolynomial ι k} (hp : p ≠ 0)
    (W : Submodule k V)
    (hW : ∀ x : V, MvPolynomial.eval (b.repr x) p ≠ 0 → x ∈ W) :
    W = ⊤ := by
  classical
  by_contra h
  obtain ⟨ℓ, hℓ, hker⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
  have hzero : p * basisLinearFormPolynomial b ℓ = 0 := by
    apply MvPolynomial.funext
    intro a
    obtain ⟨x, rfl⟩ := b.equivFun.surjective a
    change MvPolynomial.eval (b.repr x) (p * basisLinearFormPolynomial b ℓ) =
      MvPolynomial.eval (b.repr x) 0
    rw [map_mul, map_zero, eval_basisLinearFormPolynomial]
    by_cases hx : MvPolynomial.eval (b.repr x) p = 0
    · rw [hx, zero_mul]
    · have hℓx : ℓ x = 0 := hker (hW x hx)
      rw [hℓx, mul_zero]
  exact hℓ ((basisLinearFormPolynomial_eq_zero_iff b ℓ).mp
    ((mul_eq_zero.mp hzero).resolve_left hp))

/-- The nonvanishing locus of a nonzero polynomial spans the whole vector space. -/
theorem span_polynomial_nonvanishing_eq_top [Infinite k]
    (b : Basis ι k V) {p : MvPolynomial ι k} (hp : p ≠ 0) :
    Submodule.span k {x : V | MvPolynomial.eval (b.repr x) p ≠ 0} = ⊤ := by
  apply submodule_eq_top_of_polynomial_nonvanishing b hp
  intro x hx
  exact Submodule.subset_span hx

/-- A nonzero polynomial in finite basis coordinates is nonzero at some vector. -/
theorem exists_polynomial_nonvanishing [Infinite k]
    (b : Basis ι k V) {p : MvPolynomial ι k} (hp : p ≠ 0) :
    ∃ x : V, MvPolynomial.eval (b.repr x) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro a
  obtain ⟨x, rfl⟩ := b.equivFun.surjective a
  simpa using h x

end Langlands.LinearAlgebra
