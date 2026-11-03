import Mathlib.RingTheory.TensorProduct.Basic
import Langlands.CommutativeAlgebra.LocallySplit.Basic

/-! # Locally split base changes along a finite product

If `A i ⊗[R] M` is locally split over `A i` for each `i` in a finite index type, then
`(∀ i, A i) ⊗[R] M` is locally split over `∀ i, A i`. -/

open TensorProduct

namespace Langlands.CommutativeAlgebra

/-- To prove `LocallySplit R M` it suffices to factor through `κ → R` for some finite type
`κ` instead of `Fin r → R`. -/
theorem LocallySplit.of_fintype {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ (n : ℕ) (x : Fin n → M), ∃ (κ : Type*) (_ : Fintype κ) (φ : M →ₗ[R] (κ → R))
      (y : κ → M), ∀ i, ∑ j, φ (x i) j • y j = x i) :
    LocallySplit R M := by
  intro n x
  obtain ⟨κ, _, φ, y, hy⟩ := h n x
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, LinearMap.funLeft R R e.symm ∘ₗ φ, y ∘ e.symm, fun i ↦ ?_⟩
  exact (e.symm.sum_comp (fun j ↦ φ (x i) j • y j)).trans (hy i)

/-- **Product step.** If `A i ⊗[R] M` is locally split over `A i` for every `i` in a finite
index type, then `(∀ i, A i) ⊗[R] M` is locally split over `∀ i, A i`. -/
theorem locallySplit_pi {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (h : ∀ i, LocallySplit (A i) (A i ⊗[R] M)) :
    LocallySplit (∀ i, A i) ((∀ i, A i) ⊗[R] M) := by
  -- The projections to, and inclusions of, the factors `A i ⊗[R] M`.
  let π (i : ι) : (∀ i, A i) ⊗[R] M →ₗ[R] A i ⊗[R] M := (LinearMap.proj i).rTensor M
  let σ (i : ι) : A i ⊗[R] M →ₗ[R] (∀ i, A i) ⊗[R] M := (LinearMap.single R A i).rTensor M
  have hπ (i : ι) (b : ∀ i, A i) (m : (∀ i, A i) ⊗[R] M) : π i (b • m) = b i • π i m := by
    induction m with
    | tmul c m => simp [π, smul_tmul']
    | add m m' hm hm' => simp only [smul_add, map_add, hm, hm']
  have hσ (i : ι) (a : A i) (z : A i ⊗[R] M) : σ i (a • z) = Pi.single i a • σ i z := by
    induction z with
    | tmul c m => simp [σ, smul_tmul', Pi.single_mul]
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
  have hsum (m : (∀ i, A i) ⊗[R] M) : ∑ i, σ i (π i m) = m := by
    induction m with
    | tmul c m => simp [σ, π, ← sum_tmul, Finset.univ_sum_single c]
    | add m m' hm hm' => simp only [map_add, Finset.sum_add_distrib, hm, hm']
  refine LocallySplit.of_fintype fun n x ↦ ?_
  choose r φ y hy using fun i ↦ h i n (fun k ↦ π i (x k))
  let Φ : (∀ i, A i) ⊗[R] M →ₗ[∀ i, A i] ((Σ i, Fin (r i)) → ∀ i, A i) :=
    { toFun := fun m p ↦ Pi.single p.1 (φ p.1 (π p.1 m) p.2)
      map_add' := fun m m' ↦ by
        ext p : 1
        simp [Pi.single_add]
      map_smul' := fun b m ↦ by
        ext p : 1
        simp [hπ, Pi.single_mul_right] }
  refine ⟨Σ i, Fin (r i), inferInstance, Φ, fun p ↦ σ p.1 (y p.1 p.2), fun k ↦ ?_⟩
  rw [Fintype.sum_sigma]
  conv_rhs => rw [← hsum (x k)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hy i k, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hσ]
  rfl

end Langlands.CommutativeAlgebra
