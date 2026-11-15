import Langlands.CommutativeAlgebra.Popescu.Basic
import Langlands.CommutativeAlgebra.Popescu.MaximalMinors

/-! # A conormal criterion for strictly standard elements -/

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

/-- A criterion for strictly standard elements in the spirit of Stacks Lemmas 2.4 and 3.7(e).
Let `C = R[x_1, …, x_N]/(F)` and let `H_1, …, H_c` be elements of the kernel. Suppose that
`s · F_j ∈ (H) + (F)²` for every `j`, and that the Jacobian matrix `(∂H_k/∂x_i)` of the `H_k`
has a right inverse up to the scalar `t` over `C`. Then `s · t^c` is strictly standard in `C`
over `R` (for the presentation with relations `H_1, …, H_c, F_1, …, F_M`). -/
theorem isStrictlyStandard_of_conormal {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    {N M c : ℕ} (φ : MvPolynomial (Fin N) R →ₐ[R] C) (hφ : Function.Surjective φ)
    (F : Fin M → MvPolynomial (Fin N) R) (hker : RingHom.ker φ = Ideal.span (Set.range F))
    (H : Fin c → MvPolynomial (Fin N) R) (hH : ∀ k, H k ∈ RingHom.ker φ) (hcN : c ≤ N)
    (s : MvPolynomial (Fin N) R)
    (hs : ∀ j, s * F j ∈ Ideal.span (Set.range H) ⊔ RingHom.ker φ ^ 2)
    (Ψ : Matrix (Fin N) (Fin c) C) (t : C)
    (hΨ : Matrix.of (fun k i => φ (pderiv i (H k))) * Ψ = t • (1 : Matrix (Fin c) (Fin c) C)) :
    IsStrictlyStandard R (φ s * t ^ c) := by
  classical
  obtain ⟨τ, hτ⟩ := hφ t
  let F' : Fin (c + M) → MvPolynomial (Fin N) R := Fin.append H F
  have hcast : ∀ j : Fin c, Fin.castLE (Nat.le_add_right c M) j = Fin.castAdd M j :=
    fun j => Fin.ext rfl
  have hF'l : ∀ j : Fin c, F' (Fin.castAdd M j) = H j := by intro j; simp [F']
  have hF'r : ∀ j : Fin M, F' (Fin.natAdd c j) = F j := by intro j; simp [F']
  have hspan : Ideal.span (Set.range F') = RingHom.ker φ := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [hF'l]; exact hH j
      · rw [hF'r, hker]; exact Ideal.subset_span ⟨j, rfl⟩
    · rw [hker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨Fin.natAdd c j, hF'r j⟩
  have hHle : Ideal.span (Set.range H) ≤ Ideal.span (F' '' {i | (i : ℕ) < c}) := by
    apply Ideal.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨Fin.castAdd M k, by simp, hF'l k⟩
  refine ⟨N, c + M, c, hcN, Nat.le_add_right c M, F', φ, hφ, hspan.symm, ?_,
    s * τ ^ c, ?_, ?_⟩
  · -- the ideal of maximal minors
    have hmin := pow_mem_span_minors_of_mul_eq _ _ t hΨ
    have heq : (Set.range fun e : Fin c ↪o Fin N =>
        ((Matrix.of fun k i => φ (pderiv i (H k))).submatrix id e).det) =
        Set.range fun e : Fin c ↪o Fin N =>
          φ (Matrix.det fun j k : Fin c => pderiv (e k) (F' (Fin.castLE (Nat.le_add_right c M) j))) := by
      congr 1
      funext e
      change _ = φ (Matrix.det (Matrix.of fun j k : Fin c =>
        pderiv (e k) (F' (Fin.castLE (Nat.le_add_right c M) j))))
      rw [AlgHom.map_det]
      congr 1
      ext j k
      simp [hcast, hF'l]
    rw [heq] at hmin
    exact Ideal.mul_mem_left _ _ hmin
  · rw [map_mul, map_pow, hτ]
  · intro j hj
    obtain ⟨l, rfl⟩ : ∃ l : Fin M, Fin.natAdd c l = j :=
      ⟨⟨j - c, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [hF'r, mul_comm s, mul_assoc]
    refine Ideal.mul_mem_left _ _ ?_
    have := hs l
    rw [hspan]
    exact (sup_le_sup_right hHle _) this

end Langlands.CommutativeAlgebra.Popescu
