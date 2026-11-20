import Mathlib.LinearAlgebra.Lagrange

/-! # Recovering summands from weighted power sums

Let `K` be a field, `F` a `K`-vector space, `S ⊆ K` a finite set of at most `k` points and
`m : K → K` nonvanishing on `S`. For `c : K → F` put
`powerSumVector k S m c = (∑_{u ∈ S} m(u) u^j c(u))_{j < k} ∈ Fin k → F`.

If, for a family `c_l` (`l ∈ Λ`), every vector `powerSumVector k S m (c_l)` lies in the span of
the vectors `powerSumVector k S m (c_μ)` with `μ ∈ s₀`, then at every point `u₀ ∈ S` every
`c_l(u₀)` lies in the span of the `c_μ(u₀)` with `μ ∈ s₀`. The proof applies the linear map
`y ↦ m(u₀)⁻¹ ∑_j P_j y_j`, where `P = ∑_j P_j X^j` is the Lagrange basis polynomial of `S` at
`u₀` (degree `< card S ≤ k`), which sends `powerSumVector k S m c` to `c(u₀)`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Polynomial Finset

variable {K : Type*} [Field K] {F : Type*} [AddCommGroup F] [Module K F]

/-- The vector of weighted power sums `(∑_{u ∈ S} m(u) u^j c(u))_{j < k}`. -/
def powerSumVector (k : ℕ) (S : Finset K) (m : K → K) (c : K → F) : Fin k → F :=
  fun j => ∑ u ∈ S, m u • (u ^ (j : ℕ) • c u)

/-- For a polynomial `P` of degree `< k`, the linear form `y ↦ ∑_{j<k} P_j y_j` sends the
power-sum vector of `c` to `∑_{u ∈ S} m(u) P(u) c(u)`. -/
theorem sum_coeff_smul_powerSumVector {k : ℕ} (S : Finset K) (m : K → K) (c : K → F)
    {P : K[X]} (hP : P.natDegree < k) :
    ∑ j : Fin k, P.coeff j • powerSumVector k S m c j = ∑ u ∈ S, m u • (P.eval u • c u) := by
  simp only [powerSumVector, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_eq_sum_range' hP u, Finset.sum_smul, Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => m u • ((P.coeff i * u ^ i) • c u)) k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm, mul_smul]

variable {Λ : Type*}

/-- **Summands from power sums.** If `card S ≤ k`, `m` does not vanish on `S`, and every
power-sum vector `powerSumVector k S m (c l)` lies in the span of those with indices in `s₀`,
then for every `u₀ ∈ S`, every `c l u₀` lies in the span of the `c μ u₀` with `μ ∈ s₀`. -/
theorem mem_span_of_powerSumVector_mem_span {k : ℕ} {S : Finset K} (hS : S.card ≤ k)
    {m : K → K} {c : Λ → K → F} {s₀ : Set Λ}
    (h : ∀ l, powerSumVector k S m (c l) ∈
      Submodule.span K ((fun μ => powerSumVector k S m (c μ)) '' s₀))
    {u₀ : K} (hu₀ : u₀ ∈ S) (hm : m u₀ ≠ 0) (l : Λ) :
    c l u₀ ∈ Submodule.span K ((fun μ => c μ u₀) '' s₀) := by
  classical
  set P : K[X] := Lagrange.basis S id u₀ with hPdef
  have hinj : Set.InjOn (id : K → K) S := Set.injOn_id _
  have hcard : 0 < S.card := Finset.card_pos.2 ⟨u₀, hu₀⟩
  have hdeg : P.natDegree < k := by
    rw [hPdef, Lagrange.natDegree_basis hinj hu₀]
    omega
  -- the linear form recovering the summand at `u₀`
  let L : (Fin k → F) →ₗ[K] F :=
    (m u₀)⁻¹ • ∑ j : Fin k, P.coeff j • LinearMap.proj (R := K) (φ := fun _ : Fin k => F) j
  have hL : ∀ y : Fin k → F, L y = (m u₀)⁻¹ • ∑ j : Fin k, P.coeff j • y j := by
    intro y
    simp [L, LinearMap.sum_apply]
  have key : ∀ μ, L (powerSumVector k S m (c μ)) = c μ u₀ := by
    intro μ
    rw [hL, sum_coeff_smul_powerSumVector S m (c μ) hdeg,
      Finset.sum_eq_single u₀ (fun u hu hne => ?_) (fun h => absurd hu₀ h)]
    · have e : P.eval u₀ = 1 := by
        have := Lagrange.eval_basis_self (v := id) hinj hu₀
        simpa [hPdef] using this
      rw [e, one_smul, smul_smul, inv_mul_cancel₀ hm, one_smul]
    · have e : P.eval u = 0 := by
        have := Lagrange.eval_basis_of_ne (v := id) (s := S) hne.symm hu
        simpa [hPdef] using this
      rw [e, zero_smul, smul_zero]
  have hmem := Submodule.mem_map_of_mem (f := L) (h l)
  rw [Submodule.map_span, ← Set.image_comp] at hmem
  have himg : (⇑L ∘ fun μ => powerSumVector k S m (c μ)) = fun μ => c μ u₀ := funext key
  rwa [key l, himg] at hmem

end Langlands.Analysis.SeveralComplex
