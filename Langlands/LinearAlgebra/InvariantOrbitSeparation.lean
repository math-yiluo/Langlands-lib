import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Langlands.LinearAlgebra.DominantTriangularInvariants

/-! # Invariant functions separate orbits of characters -/

noncomputable section

open AddMonoidAlgebra Polynomial

namespace Langlands.LinearAlgebra.DominantTriangular

variable {M : Type*} [AddCommGroup M] {k : Type*} [Field k]

/-- Evaluation of a finitely supported function `f : M →₀ k`, viewed as a formal combination
of characters, at a homomorphism `φ : Multiplicative M →* k`: the sum `∑ μ, f μ * φ μ`. -/
def evalChar (φ : Multiplicative M →* k) : (M →₀ k) →ₗ[k] k :=
  Finsupp.linearCombination k fun μ => φ (Multiplicative.ofAdd μ)

theorem evalChar_apply (φ : Multiplicative M →* k) (f : M →₀ k) :
    evalChar φ f = f.sum fun μ a => a * φ (Multiplicative.ofAdd μ) := by
  rw [evalChar, Finsupp.linearCombination_apply]
  rfl

/-- Evaluation at `φ` as an algebra homomorphism on the group algebra. -/
private abbrev ev (φ : Multiplicative M →* k) : AddMonoidAlgebra k M →ₐ[k] k :=
  AddMonoidAlgebra.lift k k M φ

/-- The action of a linear automorphism on the group algebra. -/
private abbrev act (w : M ≃ₗ[ℤ] M) : AddMonoidAlgebra k M ≃ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.domCongr k k w.toAddEquiv

/-- The homomorphism `μ ↦ φ (w μ)`. -/
private def twist (φ : Multiplicative M →* k) (w : M ≃ₗ[ℤ] M) : Multiplicative M →* k :=
  φ.comp (AddMonoidHom.toMultiplicative (w : M →+ M))

private theorem ev_eq_evalChar (φ : Multiplicative M →* k) (x : AddMonoidAlgebra k M) :
    ev φ x = evalChar φ x.coeff := by
  rw [AddMonoidAlgebra.lift_apply, evalChar_apply]
  rfl

private theorem ev_act (φ : Multiplicative M →* k) (w : M ≃ₗ[ℤ] M) (x : AddMonoidAlgebra k M) :
    ev φ (act w x) = ev (twist φ w) x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp [twist]

private theorem act_mul (w v : M ≃ₗ[ℤ] M) (x : AddMonoidAlgebra k M) :
    act (w * v) x = act w (act v x) := by
  ext n
  simp [AddMonoidAlgebra.coeff_domCongr]
  rfl

private theorem act_one (x : AddMonoidAlgebra k M) : act 1 x = x := by
  ext n
  simp [AddMonoidAlgebra.coeff_domCongr]
  rfl

/-- **Invariant functions separate orbits.** Let `W` be a finite group of automorphisms of
`M`. If two homomorphisms `φ ψ : Multiplicative M →* k` to a field agree on every
`W`-invariant finitely supported function, then `ψ = φ ∘ w` for some `w ∈ W`. -/
theorem exists_mem_eq_of_evalChar_eq (W : Subgroup (M ≃ₗ[ℤ] M)) [Finite W]
    (φ ψ : Multiplicative M →* k)
    (h : ∀ f : M →₀ k, IsInvariant W f → evalChar φ f = evalChar ψ f) :
    ∃ w ∈ W, ∀ μ, ψ (Multiplicative.ofAdd μ) = φ (Multiplicative.ofAdd (w μ)) := by
  classical
  let _ : Fintype W := Fintype.ofFinite W
  by_contra hne
  push Not at hne
  choose μ hμ using fun w : W => hne w w.2
  let fac : W → AddMonoidAlgebra k M := fun w =>
    AddMonoidAlgebra.single (μ w) 1 -
      algebraMap k (AddMonoidAlgebra k M) (φ (Multiplicative.ofAdd ((w : M ≃ₗ[ℤ] M) (μ w))))
  let H : AddMonoidAlgebra k M := ∏ w, fac w
  have hHφ : ∀ v : W, ev φ (act v H) = 0 := by
    intro v
    rw [ev_act, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [fac, twist]
  have hHψ : ev ψ H ≠ 0 := by
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro w _
    simpa [fac, sub_eq_zero] using hμ w
  let Q : Polynomial (AddMonoidAlgebra k M) := ∏ v : W, (X - C (act v H))
  have hQinv : ∀ w ∈ W,
      Q.map ((act w : AddMonoidAlgebra k M ≃ₐ[k] AddMonoidAlgebra k M) :
        AddMonoidAlgebra k M →+* AddMonoidAlgebra k M) = Q := by
    intro w hw
    simp only [Q, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨w, hw⟩ : W)) _ _ fun v => ?_
    simp [act_mul]
  have hcoeff : ∀ n, IsInvariant W (Q.coeff n).coeff := by
    intro n w hw ν
    have h1 := congrArg (fun p : Polynomial (AddMonoidAlgebra k M) => (p.coeff n).coeff (w ν))
      (hQinv w hw)
    simp only [Polynomial.coeff_map] at h1
    rw [← h1]
    simp [AddMonoidAlgebra.coeff_domCongr]
  have hmap : Q.map (ev φ : AddMonoidAlgebra k M →+* k) =
      Q.map (ev ψ : AddMonoidAlgebra k M →+* k) := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    change ev φ _ = ev ψ _
    rw [ev_eq_evalChar, ev_eq_evalChar]
    exact h _ (hcoeff n)
  have hφQ : Q.map (ev φ : AddMonoidAlgebra k M →+* k) = X ^ Fintype.card W := by
    simp only [Q, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    simp [hHφ]
  have hψroot : (Q.map (ev ψ : AddMonoidAlgebra k M →+* k)).eval (ev ψ H) = 0 := by
    simp only [Q, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [act_one]
  rw [← hmap, hφQ, eval_pow, eval_X] at hψroot
  exact hHψ ((pow_eq_zero_iff Fintype.card_ne_zero).mp hψroot)

/-! ### Combination with triangular spanning -/

variable {ι N : Type*} [AddCommGroup N] {P : RootPairing ι ℤ M N}

/-- Invariance under every root reflection implies invariance under the reflection group. -/
theorem isInvariant_reflectionGroup_of_reflection {R : Type*} [Zero R] {f : M →₀ R}
    (hf : ∀ i μ, f (P.reflection i μ) = f μ) : IsInvariant (reflectionGroup P) f := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact hf i
  | one => exact fun μ => rfl
  | mul u v _ _ hu hv => exact fun μ => (hu (v μ)).trans (hv μ)
  | inv u _ hu =>
    intro μ
    have h := hu (u.symm μ)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- **Separation of Weyl orbits by triangular invariants.** Let `P` be a root pairing over `ℤ`
with finitely many roots and a base `b`, and let `φ ψ : Multiplicative M →* k`. Suppose every
dominant `lam` admits a reflection-group invariant `c : M →₀ k` with `c lam = 1`, support below
`lam`, and `evalChar φ c = evalChar ψ c`. Then `ψ = φ ∘ w` for some `w` in the reflection
group. -/
theorem exists_mem_reflectionGroup_of_triangular [Finite ι] (b : P.Base)
    (φ ψ : Multiplicative M →* k)
    (hc : ∀ lam : M, IsDominant P b lam → ∃ c : M →₀ k, IsInvariant (reflectionGroup P) c ∧
      c lam = 1 ∧ (∀ μ, c μ ≠ 0 → lam - μ ∈ positiveCone P b) ∧ evalChar φ c = evalChar ψ c) :
    ∃ w ∈ reflectionGroup P, ∀ μ,
      ψ (Multiplicative.ofAdd μ) = φ (Multiplicative.ofAdd (w μ)) := by
  refine exists_mem_eq_of_evalChar_eq (reflectionGroup P) φ ψ fun f hf => ?_
  have hmem : f ∈ LinearMap.ker (evalChar φ - evalChar ψ) := by
    refine isInvariant_mem_of_triangular (b := b) _ (fun lam hlam => ?_) hf
    obtain ⟨c, hcinv, hc1, hcle, hceq⟩ := hc lam hlam
    exact ⟨c, by simp [hceq], hcinv, hc1, hcle⟩
  simpa [sub_eq_zero] using hmem

end Langlands.LinearAlgebra.DominantTriangular
