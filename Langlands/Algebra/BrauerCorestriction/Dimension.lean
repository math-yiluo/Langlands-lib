import Langlands.Algebra.BrauerCorestriction.Construction

/-!
# Dimension of the tensor descent and the canonical Galois closure

The conjugate `A^σ` has the same dimension over `N` as `A` over `L`, so the tensor product of
all conjugates has dimension `(dim_L A) ^ #(L →ₐ[K] N)`, and so has the descended algebra over
`K`. The canonical closure is the normal closure of `L/K` in the separable closure of `K`. For
`L/K` finite separable it is finite Galois over `K` and admits exactly `[L : K]` embeddings
of `L`.
-/

universe u₁ u₂ u₃ u₄

open TensorProduct PiTensorProduct Module IntermediateField

namespace Langlands.BrauerCorestriction

section Dimension

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra L A]

instance conj_finiteDimensional [FiniteDimensional L A] (σ : L →ₐ[K] N) :
    FiniteDimensional N (Conj A σ) :=
  Module.Finite.trans (Twist σ) (Conj A σ)

/-- A conjugate has the same dimension as the original algebra. -/
theorem finrank_conj (σ : L →ₐ[K] N) : finrank N (Conj A σ) = finrank L A := by
  rw [← Module.finrank_mul_finrank N (Twist σ) (Conj A σ), Module.finrank_baseChange]
  have h : finrank N (Twist σ) = 1 := Module.finrank_self N
  rw [h, one_mul]

variable (K L N)

/-- The tensor product of the conjugates has dimension `(dim_L A) ^ #(L →ₐ[K] N)`. -/
theorem finrank_conjTensor [FiniteDimensional K L] [FiniteDimensional L A] :
    finrank N (ConjTensor K L N A) = finrank L A ^ Nat.card (L →ₐ[K] N) := by
  classical
  let b : ∀ σ : L →ₐ[K] N, Basis (Fin (finrank L A)) N (Conj A σ) := fun σ =>
    (Module.finBasis N (Conj A σ)).reindex (finCongr (finrank_conj A σ))
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b), Fintype.card_pi,
    Nat.card_eq_fintype_card]
  simp

/-- The descended algebra has dimension `(dim_L A) ^ #(L →ₐ[K] N)` over `K`. -/
theorem finrank_corAlg_eq_pow [FiniteDimensional K N] [IsGalois K N] [FiniteDimensional K L]
    [FiniteDimensional L A] :
    finrank K (corAlg K L N A) = finrank L A ^ Nat.card (L →ₐ[K] N) := by
  rw [finrank_corAlg, finrank_conjTensor]

/-- If `N` admits `[L : K]` embeddings of `L`, the descended algebra has dimension
`(dim_L A) ^ [L : K]`. -/
theorem finrank_corAlg_of_card [FiniteDimensional K N] [IsGalois K N] [FiniteDimensional K L]
    [FiniteDimensional L A] (hN : Nat.card (L →ₐ[K] N) = finrank K L) :
    finrank K (corAlg K L N A) = finrank L A ^ finrank K L := by
  rw [finrank_corAlg_eq_pow, hN]

end Dimension

section Closure

variable (K : Type u₁) (L : Type u₂) [Field K] [Field L] [Algebra K L]

/-- The canonical Galois closure of `L/K`: the normal closure of `L/K` inside the separable
closure of `K`, the compositum of the images of all `K`-embeddings of `L`. -/
noncomputable abbrev canonicalClosure : IntermediateField K (SeparableClosure K) :=
  normalClosure K L (SeparableClosure K)

instance canonicalClosure_isGalois : IsGalois K (canonicalClosure K L) :=
  isGalois_iff.mpr ⟨Algebra.IsSeparable.of_algHom K _ (canonicalClosure K L).val,
    normalClosure.normal K L (SeparableClosure K)⟩

instance canonicalClosure_finiteDimensional [FiniteDimensional K L] :
    FiniteDimensional K (canonicalClosure K L) :=
  normalClosure.is_finiteDimensional K L (SeparableClosure K)

/-- For `L/K` finite separable, the canonical closure admits exactly `[L : K]` embeddings
of `L`. -/
theorem natCard_algHom_canonicalClosure [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Nat.card (L →ₐ[K] canonicalClosure K L) = finrank K L := by
  rw [Nat.card_congr (normalClosure.algHomEquiv K L (SeparableClosure K))]
  exact AlgHom.natCard_of_splits K L (SeparableClosure K) fun x =>
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)

end Closure

end Langlands.BrauerCorestriction
