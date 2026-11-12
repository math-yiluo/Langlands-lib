import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Algebra for the Galois-twisted line of Conrad's Example 5.13

A separable quadratic extension `K'/K` has a nontrivial involution `σ`. For two ring maps
`μ₁ μ₂ : K' → Γ` into a commutative ring that agree on `K`, there is a unique idempotent `e` of
`Γ` such that `μ₂ = μ₁` after multiplication by `e` and `μ₂ = μ₁ ∘ σ` after multiplication by
`1 - e`: the ring `K' ⊗_K K'` is the product of two copies of `K'`.
-/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

/-- The data of a separable quadratic extension used here: a `K`-automorphism `σ` of order
dividing two, an element `θ` it moves, and the fact that `1, θ` span `K'` over `K`. -/
structure QuadraticConj (K K' : Type u) [Field K] [Field K'] [Algebra K K'] where
  /-- The conjugation. -/
  σ : K' ≃ₐ[K] K'
  /-- An element moved by the conjugation. -/
  θ : K'
  invol : ∀ x, σ (σ x) = x
  ne : σ θ ≠ θ
  span : ∀ α : K', ∃ a b : K, α = algebraMap K K' a + algebraMap K K' b * θ

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K']

/-- A separable extension of degree two carries such data. -/
theorem QuadraticConj.nonempty (h2 : Module.finrank K K' = 2) [Algebra.IsSeparable K K'] :
    Nonempty (QuadraticConj K K') := by
  have : FiniteDimensional K K' := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K K' := ⟨h2⟩
  have hcard : Nat.card (K' ≃ₐ[K] K') = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have : Fintype (K' ≃ₐ[K] K') := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (1 : K' ≃ₐ[K] K')
  have hsq : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : K' ≃ₐ[K] K' => τ x) hsq
    simpa [pow_two] using this
  obtain ⟨θ, hθ⟩ : ∃ θ, σ θ ≠ θ := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  have hind : LinearIndependent K ![(1 : K'), θ] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    apply hθ
    rw [← ha, Algebra.smul_def, mul_one, AlgEquiv.commutes]
  have htop := hind.span_eq_top_of_card_eq_finrank (by simp [h2])
  refine ⟨⟨σ, θ, hinv, hθ, fun α => ?_⟩⟩
  have hα : α ∈ Submodule.span K (Set.range ![(1 : K'), θ]) := by rw [htop]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Set.pair_comm, Submodule.mem_span_pair] at hα
  obtain ⟨a, b, hab⟩ := hα
  exact ⟨a, b, by rw [← hab, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

variable (D : QuadraticConj K K')

theorem QuadraticConj.sub_ne_zero : D.θ - D.σ D.θ ≠ 0 := sub_ne_zero_of_ne D.ne.symm

/-- Elements fixed by the conjugation lie in `K`. -/
theorem QuadraticConj.exists_eq_of_fixed {α : K'} (h : D.σ α = α) :
    ∃ a : K, α = algebraMap K K' a := by
  obtain ⟨a, b, rfl⟩ := D.span α
  refine ⟨a, ?_⟩
  have hσ : D.σ (algebraMap K K' a + algebraMap K K' b * D.θ) =
      algebraMap K K' a + algebraMap K K' b * D.σ D.θ := by
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes]
  rw [hσ] at h
  have hb : algebraMap K K' b * (D.θ - D.σ D.θ) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp hb with hb | hb
  · rw [hb, zero_mul, add_zero]
  · exact absurd hb D.sub_ne_zero

variable {Γ : Type*} [CommRing Γ]

/-- The idempotent of `Γ` on which `μ₂` agrees with `μ₁`. -/
def splitIdem (μ₁ μ₂ : K' →+* Γ) : Γ :=
  (μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹

variable {D} {μ₁ μ₂ : K' →+* Γ}

theorem splitIdem_quad (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k)) :
    (μ₂ D.θ - μ₁ D.θ) * (μ₂ D.θ - μ₁ (D.σ D.θ)) = 0 := by
  obtain ⟨s0, hs0⟩ := D.exists_eq_of_fixed (α := D.θ + D.σ D.θ)
    (by rw [map_add, D.invol, add_comm])
  obtain ⟨n0, hn0⟩ := D.exists_eq_of_fixed (α := D.θ * D.σ D.θ)
    (by rw [map_mul, D.invol, mul_comm])
  have h1 : μ₁ D.θ + μ₁ (D.σ D.θ) = μ₂ D.θ + μ₂ (D.σ D.θ) := by
    rw [← map_add, ← map_add, hs0, hμ]
  have h2 : μ₁ D.θ * μ₁ (D.σ D.θ) = μ₂ D.θ * μ₂ (D.σ D.θ) := by
    rw [← map_mul, ← map_mul, hn0, hμ]
  linear_combination (-(μ₂ D.θ)) * h1 + h2

theorem splitIdem_unit :
    μ₁ (D.θ - D.σ D.θ) * μ₁ (D.θ - D.σ D.θ)⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ D.sub_ne_zero, map_one]

theorem splitIdem_mul_θ (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k)) :
    splitIdem D μ₁ μ₂ * (μ₂ D.θ - μ₁ D.θ) = 0 := by
  unfold splitIdem
  linear_combination (μ₁ (D.θ - D.σ D.θ)⁻¹) * splitIdem_quad hμ

theorem one_sub_splitIdem_mul_θ
    (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k)) :
    (1 - splitIdem D μ₁ μ₂) * (μ₂ D.θ - μ₁ (D.σ D.θ)) = 0 := by
  unfold splitIdem
  have hu := splitIdem_unit (D := D) (μ₁ := μ₁)
  rw [map_sub] at hu
  linear_combination (-(μ₂ D.θ - μ₁ (D.σ D.θ))) * hu -
    (μ₁ (D.θ - D.σ D.θ)⁻¹) * splitIdem_quad hμ

theorem splitIdem_isIdempotentElem
    (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k)) :
    IsIdempotentElem (splitIdem D μ₁ μ₂) := by
  have h := one_sub_splitIdem_mul_θ (D := D) hμ
  unfold IsIdempotentElem
  have : splitIdem D μ₁ μ₂ * (1 - splitIdem D μ₁ μ₂) = 0 := by
    unfold splitIdem at h ⊢
    linear_combination (μ₁ (D.θ - D.σ D.θ)⁻¹) * h
  linear_combination -this

theorem splitIdem_mul (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k))
    (α : K') : splitIdem D μ₁ μ₂ * (μ₂ α - μ₁ α) = 0 := by
  obtain ⟨a, b, rfl⟩ := D.span α
  simp only [map_add, map_mul]
  rw [hμ a, hμ b]
  linear_combination (μ₂ (algebraMap K K' b)) * splitIdem_mul_θ hμ

theorem one_sub_splitIdem_mul
    (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k)) (α : K') :
    (1 - splitIdem D μ₁ μ₂) * (μ₂ α - μ₁ (D.σ α)) = 0 := by
  obtain ⟨a, b, rfl⟩ := D.span α
  simp only [map_add, map_mul, AlgEquiv.commutes]
  rw [hμ a, hμ b]
  linear_combination (μ₂ (algebraMap K K' b)) * one_sub_splitIdem_mul_θ hμ

/-- The idempotent is unique. -/
theorem splitIdem_unique (hμ : ∀ k : K, μ₁ (algebraMap K K' k) = μ₂ (algebraMap K K' k))
    {e : Γ} (h₁ : ∀ α, e * (μ₂ α - μ₁ α) = 0)
    (h₂ : ∀ α, (1 - e) * (μ₂ α - μ₁ (D.σ α)) = 0) : e = splitIdem D μ₁ μ₂ := by
  have hu := splitIdem_unit (D := D) (μ₁ := μ₁)
  rw [map_sub] at hu
  have hA := h₁ D.θ
  have hC := h₂ D.θ
  have hB := one_sub_splitIdem_mul_θ (D := D) hμ
  have hD := splitIdem_mul_θ (D := D) hμ
  unfold splitIdem at hB hD ⊢
  have hef : e * (1 - (μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹) = 0 := by
    linear_combination (-(e * (1 - (μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹))) * hu +
      (μ₁ (D.θ - D.σ D.θ)⁻¹ * e) * hB -
      (μ₁ (D.θ - D.σ D.θ)⁻¹ * (1 - (μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹)) * hA
  have hfe : (μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹ * (1 - e) = 0 := by
    linear_combination (-((μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹ * (1 - e))) * hu +
      (μ₁ (D.θ - D.σ D.θ)⁻¹ * ((μ₂ D.θ - μ₁ (D.σ D.θ)) * μ₁ (D.θ - D.σ D.θ)⁻¹)) * hC -
      (μ₁ (D.θ - D.σ D.θ)⁻¹ * (1 - e)) * hD
  linear_combination hef - hfe

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
