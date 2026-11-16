import Langlands.Representation.Archimedean.RealPolynomialFunctions
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrix-valued real polynomial maps

`IsPolyMat ι d M`: every entry of the matrix-valued map `M : (ι → ℂ) → Matrix κ κ' ℂ` is a real
polynomial of degree `≤ d` in the coordinates `v_k`, `conj v_k` (`degLE ι d`). Closure under
sums, products, determinants, adjugates, conjugate transposes and submatrices.
-/

noncomputable section

open scoped Matrix ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.RealPolynomialFunctions

variable {ι : Type*} [Fintype ι]

/-- All entries of `M` have degree `≤ d`. -/
def IsPolyMat {κ κ' : Type*} (d : ℕ) (M : (ι → ℂ) → Matrix κ κ' ℂ) : Prop :=
  ∀ a b, (fun v => M v a b) ∈ degLE ι d

variable {κ κ' κ'' : Type*}

theorem IsPolyMat.mono {a b : ℕ} {M : (ι → ℂ) → Matrix κ κ' ℂ} (h : IsPolyMat a M) (hab : a ≤ b) :
    IsPolyMat b M := fun x y => degLE_mono hab (h x y)

theorem isPolyMat_const (C : Matrix κ κ' ℂ) (d : ℕ) : IsPolyMat (ι := ι) d (fun _ => C) :=
  fun _ _ => const_mem_degLE _ d

theorem IsPolyMat.add {d : ℕ} {M N : (ι → ℂ) → Matrix κ κ' ℂ} (hM : IsPolyMat d M)
    (hN : IsPolyMat d N) : IsPolyMat d (fun v => M v + N v) := fun a b => by
  have : (fun v => (M v + N v) a b) = (fun v => M v a b) + fun v => N v a b := rfl
  rw [this]; exact Submodule.add_mem _ (hM a b) (hN a b)

theorem IsPolyMat.sub {d : ℕ} {M N : (ι → ℂ) → Matrix κ κ' ℂ} (hM : IsPolyMat d M)
    (hN : IsPolyMat d N) : IsPolyMat d (fun v => M v - N v) := fun a b => by
  have : (fun v => (M v - N v) a b) = (fun v => M v a b) - fun v => N v a b := rfl
  rw [this]; exact Submodule.sub_mem _ (hM a b) (hN a b)

theorem IsPolyMat.mul [Fintype κ'] {a b : ℕ} {M : (ι → ℂ) → Matrix κ κ' ℂ}
    {N : (ι → ℂ) → Matrix κ' κ'' ℂ} (hM : IsPolyMat a M) (hN : IsPolyMat b N) :
    IsPolyMat (a + b) (fun v => M v * N v) := fun x y => by
  have : (fun v => (M v * N v) x y) = ∑ k, (fun v => M v x k) * fun v => N v k y := by
    funext v; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun k _ => mul_mem_degLE (hM x k) (hN k y)

theorem IsPolyMat.conjTranspose {d : ℕ} {M : (ι → ℂ) → Matrix κ κ' ℂ} (hM : IsPolyMat d M) :
    IsPolyMat d (fun v => (M v)ᴴ) := fun a b => by
  have : (fun v => (M v)ᴴ a b) = fun v => conj (M v b a) := by
    funext v; simp [Matrix.conjTranspose_apply]
  rw [this]; exact conj_mem_degLE (hM b a)

theorem IsPolyMat.submatrix {d : ℕ} {M : (ι → ℂ) → Matrix κ κ' ℂ} (hM : IsPolyMat d M)
    {μ μ' : Type*} (f : μ → κ) (g : μ' → κ') : IsPolyMat d (fun v => (M v).submatrix f g) :=
  fun a b => hM (f a) (g b)

theorem IsPolyMat.det [Fintype κ] [DecidableEq κ] {a : ℕ} {M : (ι → ℂ) → Matrix κ κ ℂ}
    (hM : IsPolyMat a M) : (fun v => (M v).det) ∈ degLE ι (Fintype.card κ * a) := by
  have : (fun v => (M v).det) = ∑ σ : Equiv.Perm κ,
      (Equiv.Perm.sign σ : ℤ) • ∏ x : κ, fun v => M v (σ x) x := by
    funext v
    simp only [Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def]
  rw [this]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_of_tower_mem _ _ ?_
  have := prod_mem_degLE (ι := ι) Finset.univ (fun x : κ => fun v => M v (σ x) x) (fun _ => a)
    fun x _ => hM (σ x) x
  simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using this

theorem IsPolyMat.adjugate [Fintype κ] [DecidableEq κ] {a : ℕ} {M : (ι → ℂ) → Matrix κ κ ℂ}
    (hM : IsPolyMat a M) : IsPolyMat (Fintype.card κ * a) (fun v => (M v).adjugate) := by
  intro x y
  have hU : IsPolyMat a (fun v => (M v).updateRow y (Pi.single x 1)) := by
    intro c d
    by_cases hc : c = y
    · subst hc
      simp only [Matrix.updateRow_self]
      exact const_mem_degLE _ a
    · simp only [Matrix.updateRow_ne hc]
      exact hM c d
  have := hU.det
  simpa [Matrix.adjugate_apply] using this

end Langlands.Archimedean.RealPolynomialFunctions
