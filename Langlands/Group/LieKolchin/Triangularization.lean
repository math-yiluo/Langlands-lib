import Langlands.Algebra.GradedHopf.Triangular
import Langlands.Group.LieKolchin.CommonEigenvector

/-! # Simultaneous triangularization of connected solvable matrix groups

A matrix representation `ρ : G →* Matrix (Fin n) (Fin n) k` of a connected solvable group
with separately continuous group laws, over an algebraically closed field, whose linear
conditions `Λ (ρ g) = c` are closed, is conjugate to a representation by upper triangular
matrices. -/

open scoped commutatorElement Matrix

namespace Langlands.LieKolchin

open Langlands.Algebra.GradedHopf.Triangular

section Blocks

variable {k : Type*} [Field k] {n : ℕ}

/-- Multiplying by `stepP v i₀` on the right turns the first column into `M *ᵥ v`. -/
theorem mul_stepP_apply_zero (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (v : Fin (n + 1) → k) (i₀ i : Fin (n + 1)) : (M * stepP v i₀) i 0 = (M *ᵥ v) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, stepP]

theorem ext1_mul_mul_succ_zero (Q P : Matrix (Fin n) (Fin n) k)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hb : ∀ i : Fin n, b i.succ 0 = 0)
    (i : Fin n) : (ext1 Q * b * ext1 P) i.succ 0 = 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, hb]

theorem ext1_mul_mul_succ_succ (Q P : Matrix (Fin n) (Fin n) k)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (i j : Fin n) :
    (ext1 Q * b * ext1 P) i.succ j.succ = (Q * b.submatrix Fin.succ Fin.succ * P) i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_mul]

end Blocks

variable {k G : Type*} [Field k] [IsAlgClosed k] [Group G] [TopologicalSpace G]

/-- A common eigenvector of a connected solvable matrix group. -/
theorem exists_mulVec_eigenvector [PreconnectedSpace G] [Group.IsSolvable G]
    (hmul : ∀ a : G, Continuous fun x => a * x) (hinv : Continuous fun x : G => x⁻¹)
    (hcomm : ∀ a : G, Continuous fun x : G => ⁅a, x⁆) {n : ℕ}
    (ρ : G →* Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (hR : ∀ (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) k →ₗ[k] k) (c : k),
      IsClosed {g : G | Λ (ρ g) = c}) :
    ∃ v : Fin (n + 1) → k, v ≠ 0 ∧ ∀ g, ∃ c : k, ρ g *ᵥ v = c • v := by
  let e := (Matrix.toLinAlgEquiv' : Matrix (Fin (n + 1)) (Fin (n + 1)) k ≃ₐ[k] _)
  let ρE : G →* Module.End k (Fin (n + 1) → k) := e.toRingEquiv.toMonoidHom.comp ρ
  have hRE : ∀ (Λ : Module.End k (Fin (n + 1) → k) →ₗ[k] k) (c : k),
      IsClosed {g : G | Λ (ρE g) = c} := fun Λ c => hR (Λ ∘ₗ e.toLinearMap) c
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_isSolvable hmul hinv hcomm ρE hRE
  exact ⟨v, hv0, hv⟩

/-- **Lie–Kolchin for matrices.** A connected solvable matrix group whose linear conditions are
closed is conjugate to a group of upper triangular matrices: there are mutually inverse
`P` and `Q` with every `Q * ρ g * P` upper triangular. -/
theorem exists_triangularizing [PreconnectedSpace G] [Group.IsSolvable G]
    (hmul : ∀ a : G, Continuous fun x => a * x) (hinv : Continuous fun x : G => x⁻¹)
    (hcomm : ∀ a : G, Continuous fun x : G => ⁅a, x⁆) :
    ∀ (n : ℕ) (ρ : G →* Matrix (Fin n) (Fin n) k),
      (∀ (Λ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (c : k), IsClosed {g : G | Λ (ρ g) = c}) →
      ∃ P Q : Matrix (Fin n) (Fin n) k, P * Q = 1 ∧
        ∀ g (i j : Fin n), j < i → (Q * ρ g * P) i j = 0 := by
  intro n
  induction n with
  | zero =>
    intro ρ _
    exact ⟨1, 1, Matrix.mul_one 1, fun _ i => i.elim0⟩
  | succ n ih =>
    intro ρ hR
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eigenvector hmul hinv hcomm ρ hR
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hv0
    set P₁ := stepP v i₀
    set Q₁ := stepQ v i₀
    have hQP : Q₁ * P₁ = 1 := stepQ_mul_stepP v i₀ hi₀
    have hPQ : P₁ * Q₁ = 1 := mul_eq_one_comm.1 hQP
    let B : G → Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun g => Q₁ * ρ g * P₁
    have hB0 : ∀ g (i : Fin n), B g i.succ 0 = 0 := by
      intro g i
      obtain ⟨c, hc⟩ := hv g
      have hQv : Q₁ *ᵥ v = fun i => (Q₁ * P₁) i 0 := by
        ext l
        rw [mul_stepP_apply_zero]
      change (Q₁ * ρ g * stepP v i₀) i.succ 0 = 0
      rw [mul_stepP_apply_zero, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hQv, hQP]
      simp [Matrix.one_apply_ne (Fin.succ_ne_zero i)]
    have hBmul : ∀ g h, B (g * h) = B g * B h := by
      intro g h
      simp only [B, map_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P₁ Q₁, hPQ, Matrix.one_mul]
    let ρ₂ : G →* Matrix (Fin n) (Fin n) k :=
      { toFun := fun g => (B g).submatrix Fin.succ Fin.succ
        map_one' := by
          simp only [B, map_one, Matrix.mul_one, hQP]
          exact Matrix.submatrix_one _ (Fin.succ_injective _)
        map_mul' := fun g h => by
          ext i j
          simp [hBmul, Matrix.mul_apply, Fin.sum_univ_succ, hB0] }
    let L : Matrix (Fin (n + 1)) (Fin (n + 1)) k →ₗ[k] Matrix (Fin n) (Fin n) k :=
      { toFun := fun M => (Q₁ * M * P₁).submatrix Fin.succ Fin.succ
        map_add' := fun M N => by
          rw [Matrix.mul_add, Matrix.add_mul]
          rfl
        map_smul' := fun c M => by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          rfl }
    have hR₂ : ∀ (Λ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (c : k),
        IsClosed {g : G | Λ (ρ₂ g) = c} := fun Λ c => hR (Λ ∘ₗ L) c
    obtain ⟨P₂, Q₂, hPQ₂, htri⟩ := ih ρ₂ hR₂
    refine ⟨P₁ * ext1 P₂, ext1 Q₂ * Q₁, ?_, fun g i j hji => ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (ext1 P₂), ext1_mul, hPQ₂, ext1_one,
        Matrix.one_mul, hPQ]
    · have hE : ext1 Q₂ * Q₁ * ρ g * (P₁ * ext1 P₂) = ext1 Q₂ * B g * ext1 P₂ := by
        simp only [B, Matrix.mul_assoc]
      rw [hE]
      induction i using Fin.cases with
      | zero => exact absurd hji (Fin.not_lt_zero j)
      | succ i =>
        induction j using Fin.cases with
        | zero => exact ext1_mul_mul_succ_zero Q₂ P₂ (B g) (hB0 g) i
        | succ j =>
          rw [ext1_mul_mul_succ_succ]
          exact htri g i j (Fin.succ_lt_succ_iff.1 hji)

end Langlands.LieKolchin
