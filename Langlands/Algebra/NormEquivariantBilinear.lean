import Mathlib.FieldTheory.Fixed
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Trace compatibility of norm-equivariant bilinear maps -/

noncomputable section

open Module

namespace Langlands.Algebra.NormEquivariantBilinear

variable {k E L : Type*} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]

/-- Coefficients of products of two embeddings are unique. -/
theorem coeff_eq_zero [Fintype (E →ₐ[k] L)] {a : (E →ₐ[k] L) → (E →ₐ[k] L) → L}
    (h : ∀ x y : E, ∑ τ, ∑ ρ, a τ ρ * τ x * ρ y = 0) (τ ρ : E →ₐ[k] L) : a τ ρ = 0 := by
  have hli := Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap k E L)
  have hrow : ∀ y : E, ∀ τ, ∑ ρ, a τ ρ * ρ y = 0 := by
    intro y
    refine hli (fun τ => ∑ ρ, a τ ρ * ρ y) ?_
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply, smul_eq_mul, LinearMap.zero_apply]
    rw [← h x y]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  refine hli (fun ρ => a τ ρ) ?_ ρ
  ext y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul, LinearMap.zero_apply]
  exact hrow y τ

variable [FiniteDimensional k E]

/-- With as many embeddings as the degree, the embeddings form a basis of the `k`-linear
maps `E → L`. -/
def embeddingBasis [Fintype (E →ₐ[k] L)] (hcard : Nat.card (E →ₐ[k] L) = finrank k E) :
    Basis (E →ₐ[k] L) L (E →ₗ[k] L) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun τ => τ.toLinearMap)
    (linearIndependent_algHom_toLinearMap k E L)
    (by rw [Fintype.card_eq_nat_card, hcard, Module.finrank_linearMap_self])

theorem embeddingBasis_apply [Fintype (E →ₐ[k] L)] (hcard : Nat.card (E →ₐ[k] L) = finrank k E)
    (τ : E →ₐ[k] L) : embeddingBasis hcard τ = τ.toLinearMap := by
  simp [embeddingBasis]

/-- Every `k`-linear map `E → L` is an `L`-combination of embeddings. -/
theorem linearMap_eq_sum [Fintype (E →ₐ[k] L)] (hcard : Nat.card (E →ₐ[k] L) = finrank k E)
    (φ : E →ₗ[k] L) (x : E) :
    φ x = ∑ τ, (embeddingBasis hcard).repr φ τ * τ x := by
  conv_lhs => rw [← (embeddingBasis hcard).sum_repr φ]
  simp [embeddingBasis_apply]

/-- Every `k`-bilinear map `E × E → L` is an `L`-combination of products of embeddings. -/
theorem exists_coeff [Fintype (E →ₐ[k] L)] (hcard : Nat.card (E →ₐ[k] L) = finrank k E)
    (B : E →ₗ[k] E →ₗ[k] L) :
    ∃ a : (E →ₐ[k] L) → (E →ₐ[k] L) → L,
      ∀ x y : E, B x y = ∑ τ, ∑ ρ, a τ ρ * τ x * ρ y := by
  let b := embeddingBasis hcard
  let A : (E →ₐ[k] L) → E →ₗ[k] L := fun ρ =>
    ((Finsupp.lapply (R := L) (M := L) ρ).restrictScalars k ∘ₗ
      b.repr.toLinearMap.restrictScalars k) ∘ₗ B
  have hA : ∀ ρ x, A ρ x = b.repr (B x) ρ := fun _ _ => rfl
  refine ⟨fun τ ρ => b.repr (A ρ) τ, fun x y => ?_⟩
  rw [linearMap_eq_sum hcard (B x) y]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← hA, linearMap_eq_sum hcard (A ρ) x, Finset.sum_mul]

/-- **Trace compatibility from norm equivariance.** Let `B : E × E → E` be `k`-bilinear and
`σ` a `k`-endomorphism of `E`. Suppose that `B (c x) (c y) = c σ(c) B x y` for all `c` in a
set `C`, and that the characters `c ↦ τ(c) ρ(c)` on `C` separate every pair of embeddings
`(τ, ρ)` into `L` from the two pairs `(π, π σ)` and `(π σ, π)`. If `E` has `[E : k]`
embeddings into `L`, then `B (f x) y + B x (f y) = (f + σ f) B x y`. -/
theorem add_eq_trace_mul [Fintype (E →ₐ[k] L)] (hcard : Nat.card (E →ₐ[k] L) = finrank k E)
    (σ : E →ₐ[k] E) (C : Set E) (B : E →ₗ[k] E →ₗ[k] E)
    (hnorm : ∀ c ∈ C, ∀ x y : E, B (c * x) (c * y) = c * σ c * B x y)
    (hsep : ∀ π τ ρ : E →ₐ[k] L, (∀ c ∈ C, τ c * ρ c = π c * π (σ c)) →
      (τ = π ∧ ρ = π.comp σ) ∨ (τ = π.comp σ ∧ ρ = π))
    (f x y : E) : B (f * x) y + B x (f * y) = (f + σ f) * B x y := by
  have hne : Nonempty (E →ₐ[k] L) :=
    (Nat.card_pos_iff.mp (by rw [hcard]; exact Module.finrank_pos)).1
  obtain ⟨π⟩ := hne
  apply π.toRingHom.injective
  change π (B (f * x) y + B x (f * y)) = π ((f + σ f) * B x y)
  obtain ⟨a, ha⟩ := exists_coeff hcard (B.compr₂ π.toLinearMap)
  have ha' : ∀ x y : E, π (B x y) = ∑ τ, ∑ ρ, a τ ρ * τ x * ρ y := ha
  -- Equivariance kills every coefficient outside the two conjugate pairs.
  have hcoeff : ∀ c ∈ C, ∀ τ ρ, a τ ρ * (τ c * ρ c - π c * π (σ c)) = 0 := by
    intro c hc
    refine coeff_eq_zero fun x y => ?_
    have h1 := ha' (c * x) (c * y)
    rw [hnorm c hc, map_mul, map_mul, ha'] at h1
    have h2 : ∑ τ, ∑ ρ, a τ ρ * (τ c * ρ c - π c * π (σ c)) * τ x * ρ y =
        (∑ τ, ∑ ρ, a τ ρ * τ (c * x) * ρ (c * y)) -
          π c * π (σ c) * ∑ τ, ∑ ρ, a τ ρ * τ x * ρ y := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [map_mul, map_mul]
      ring
    rw [h2, ← h1, sub_self]
  have hterm : ∀ τ ρ : E →ₐ[k] L, a τ ρ * (τ f + ρ f) = a τ ρ * π (f + σ f) := by
    intro τ ρ
    by_cases h0 : a τ ρ = 0
    · rw [h0, zero_mul, zero_mul]
    · have hall : ∀ c ∈ C, τ c * ρ c = π c * π (σ c) := fun c hc =>
        sub_eq_zero.mp ((mul_eq_zero.mp (hcoeff c hc τ ρ)).resolve_left h0)
      rcases hsep π τ ρ hall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [map_add, AlgHom.comp_apply]
      · rw [map_add, AlgHom.comp_apply, add_comm]
  rw [map_add, ha', ha', map_mul, ha', Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have := hterm τ ρ
  rw [map_mul, map_mul]
  linear_combination (τ x * ρ y) * this

end Langlands.Algebra.NormEquivariantBilinear
