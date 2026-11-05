import Langlands.GroupScheme.Reductive.RankOneSteinbergOperators
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RepresentationTheory.Irreducible

/-! # Recovering divided powers from polynomial root actions -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.RankOneSteinberg

section Coefficients

variable (k : Type u) [Field k] {n : Type v} {N : ℕ}

/-- The inverse Vandermonde row that recovers one coefficient from the sampled values. -/
def coefficientWeights (t : Fin N → k) (i : Fin N) : Fin N → k :=
  (Matrix.vandermonde t)⁻¹ i

/-- Explicit recovery of every vector coefficient from distinct samples. -/
theorem coefficient_reconstruction (t : Fin N → k) (ht : Function.Injective t)
    (f : Fin N → n → k) (i : Fin N) :
    f i = ∑ a, coefficientWeights k t i a • (∑ r : Fin N, t a ^ (r : ℕ) • f r) := by
  let F : Matrix (Fin N) n k := f
  have h := Matrix.nonsing_inv_mul_cancel_left (Matrix.vandermonde t) F
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ht))
  ext c
  have hc := congrArg (fun M : Matrix (Fin N) n k => M i c) h
  change (∑ a, (Matrix.vandermonde t)⁻¹ i a *
    (∑ r : Fin N, t a ^ (r : ℕ) * f r c)) = f i c at hc
  simpa only [coefficientWeights, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc.symm

/-- A vector subspace containing every polynomial value contains each coefficient. -/
theorem coefficient_mem_of_values_mem [Infinite k]
    (f : Fin N → n → k) (W : Submodule k (n → k))
    (h : ∀ t : k, (∑ r : Fin N, t ^ (r : ℕ) • f r) ∈ W) (i : Fin N) : f i ∈ W := by
  let t : Fin N → k := fun a => Infinite.natEmbedding k a
  have ht : Function.Injective t := (Infinite.natEmbedding k).injective.comp Fin.val_injective
  rw [coefficient_reconstruction k t ht f i]
  exact W.sum_mem fun a _ => W.smul_mem _ (h (t a))

end Coefficients

section PolynomialMatrices

variable (k : Type u) [Field k] (m : ℕ)

/-- The finite polynomial family formed from all raising divided powers. -/
def upperMatrix (t : k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  ∑ a : Fin (m + 1), t ^ (a : ℕ) • raising k m a

/-- The finite polynomial family formed from all lowering divided powers. -/
def lowerMatrix (t : k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  ∑ a : Fin (m + 1), t ^ (a : ℕ) • lowering k m a

theorem upperMatrix_mulVec (t : k) (x : Fin (m + 1) → k) :
    upperMatrix k m t *ᵥ x =
      ∑ a : Fin (m + 1), t ^ (a : ℕ) • (raising k m a *ᵥ x) := by
  ext i
  simp only [upperMatrix, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, Finset.sum_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem lowerMatrix_mulVec (t : k) (x : Fin (m + 1) → k) :
    lowerMatrix k m t *ᵥ x =
      ∑ a : Fin (m + 1), t ^ (a : ℕ) • (lowering k m a *ᵥ x) := by
  ext i
  simp only [lowerMatrix, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, Finset.sum_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Polynomial point stability constructs stability under every divided-power operator. -/
def invariantOfPolynomialStable [Infinite k] (W : Submodule k (Fin (m + 1) → k))
    (hupper : ∀ t x, x ∈ W → upperMatrix k m t *ᵥ x ∈ W)
    (hlower : ∀ t x, x ∈ W → lowerMatrix k m t *ᵥ x ∈ W) :
    DividedPowerInvariantSubmodule k m := by
  refine ⟨W, ?_, ?_⟩
  · intro a x hx
    by_cases ha : a ≤ m
    · exact coefficient_mem_of_values_mem k (fun r : Fin (m + 1) => raising k m r *ᵥ x)
        W (fun t => by rw [← upperMatrix_mulVec]; exact hupper t x hx)
        ⟨a, by omega⟩
    · have hz : raising k m a = 0 := by
        simp [raising, SplitExistence.gamE_eq_zero (by omega : m < a)]
      simp [hz]
  · intro a x hx
    by_cases ha : a ≤ m
    · exact coefficient_mem_of_values_mem k (fun r : Fin (m + 1) => lowering k m r *ᵥ x)
        W (fun t => by rw [← lowerMatrix_mulVec]; exact hlower t x hx)
        ⟨a, by omega⟩
    · have hz : lowering k m a = 0 := by
        simp [lowering, SplitExistence.gamF_eq_zero (by omega : m < a)]
      simp [hz]

end PolynomialMatrices

section Representations

variable {k : Type u} [Field k] [Infinite k] {Γ : Type w} [Monoid Γ]
  (p : ℕ) [Fact p.Prime] [CharP k p] (s : ℕ)
  (ρ : Representation k Γ (Fin (p ^ s - 1 + 1) → k))

/-- Actual elements of a represented monoid realizing the two polynomial root families. -/
structure PolynomialRootRealization where
  upperPoint : k → Γ
  lowerPoint : k → Γ
  upper_action : ∀ t x, ρ (upperPoint t) x = upperMatrix k (p ^ s - 1) t *ᵥ x
  lower_action : ∀ t x, ρ (lowerPoint t) x = lowerMatrix k (p ^ s - 1) t *ᵥ x

/-- The polynomial root formulas imply irreducibility of the supplied actual representation. -/
theorem irreducible_of_polynomialRootRealization (D : PolynomialRootRealization p s ρ) :
    ρ.IsIrreducible := by
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    have hh : (⊥ : Submodule k (Fin (p ^ s - 1 + 1) → k)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  · intro W
    let W' : DividedPowerInvariantSubmodule k (p ^ s - 1) :=
      invariantOfPolynomialStable k _ W.toSubmodule
        (fun t x hx => by
          rw [← D.upper_action t x]
          exact W.apply_mem_toSubmodule _ hx)
        (fun t x hx => by
          rw [← D.lower_action t x]
          exact W.apply_mem_toSubmodule _ hx)
    rcases steinberg_invariant_eq_bot_or_top k p s W' with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Representations

end Langlands.GroupScheme.RankOneSteinberg
