import Langlands.GroupScheme.MatrixRepresentation.AdditiveTensorAlgebra
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability

/-! # Actual tensor irreducibility from additive coefficient fullness -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveTensorIrreducibility

open AdditiveDividedPowers AdditiveTensorAlgebra

variable {k : Type u} [Field k]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The matrices preserving a specified ground-field subspace. -/
def invariantAlgebra (W : Submodule k (n → k)) : Subalgebra k (Matrix n n k) where
  carrier := {M | ∀ v ∈ W, M *ᵥ v ∈ W}
  algebraMap_mem' c := by
    intro v hv
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem c hv
  add_mem' := by
    intro A B hA hB v hv
    rw [Matrix.add_mulVec]
    exact W.add_mem (hA v hv) (hB v hv)
  mul_mem' := by
    intro A B hA hB v hv
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hB v hv)

variable {I : Type v}
  (ρs : I → MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- All-test stability for each supplied additive representation is exactly
containment of its family's matrix coefficient algebra in the preserving algebra. -/
theorem coefficientAlgebra_le_invariantAlgebra_iff (W : Submodule k (n → k)) :
    coefficientAlgebra ρs ≤ invariantAlgebra W ↔
      ∀ i, (ρs i).IsStableSubspace W := by
  constructor
  · intro h i
    apply (AdditiveInvariantSubspaces.isStableSubspace_iff_invariant_dividedPower
      (ρs i) W).mpr
    intro d v hv
    have hd := h (coefficientMatrix_mem_coefficientAlgebra ρs i d) v hv
    rw [dividedPower_eq_toLin]
    exact hd
  · intro h
    apply Algebra.adjoin_le
    rintro _ ⟨⟨i, d⟩, rfl⟩ v hv
    have hd := (AdditiveInvariantSubspaces.isStableSubspace_iff_invariant_dividedPower
      (ρs i) W).mp (h i) d v hv
    rw [dividedPower_eq_toLin] at hd
    exact hd

/-- A subspace stable for a family with full coefficient algebra is zero or
the entire original coordinate space, over finite as well as infinite fields. -/
theorem eq_bot_or_eq_top_of_coefficientAlgebra_eq_top
    (hfull : coefficientAlgebra ρs = ⊤)
    (W : Submodule k (n → k)) (hW : ∀ i, (ρs i).IsStableSubspace W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  have hle := (coefficientAlgebra_le_invariantAlgebra_iff ρs W).mpr hW
  rw [hfull] at hle
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hW0
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  change v j ≠ 0 at hj
  apply top_unique
  intro w _
  let M : Matrix n n k := fun i l => if l = j then w i / v j else 0
  have hMv : M *ᵥ v = w := by
    funext i
    change (∑ l, M i l * v l) = w i
    rw [Finset.sum_eq_single j]
    · simp [M, div_mul_cancel₀ _ hj]
    · intro l _ hlj
      simp [M, hlj]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  rw [← hMv]
  exact hle (show M ∈ (⊤ : Subalgebra k (Matrix n n k)) from by trivial) v hv

section Ambient

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (ρ : MatrixRepresentation G n)
  (f : I → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))

/-- Restricting the actual action preserves all-test stable subspaces. -/
theorem isStableSubspace_restrict_of_isStableSubspace
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) (i : I) :
    (ρ.restrict (f i)).IsStableSubspace W := by
  intro A x v hv ℓ
  change (fun j => ℓ ((((ρ.restrict (f i)).affineMatrix A x : Matrix n n A) *ᵥ
    (fun a => algebraMap k A (v a))) j)) ∈ W
  rw [affineMatrix_restrict]
  exact hW A (x ≫ (f i).hom.hom) v hv ℓ

/-- Full coefficients of supplied additive restrictions imply irreducibility
of the original ambient representation on its entire nonzero coordinate space. -/
theorem isIrreducible_of_coefficientAlgebra_eq_top [Nonempty n]
    (hfull : coefficientAlgebra (fun i => ρ.restrict (f i)) = ⊤) :
    ρ.IsIrreducible := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  exact eq_bot_or_eq_top_of_coefficientAlgebra_eq_top _ hfull W
    (isStableSubspace_restrict_of_isStableSubspace ρ f hW)

variable (σ : MatrixRepresentation G m) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Conditional irreducibility of the actual diagonal Frobenius tensor.
The two coefficient fullness premises concern the supplied actual restrictions. -/
theorem isIrreducible_tensor_frobeniusPower [Nonempty n] [Nonempty m] (e : ℕ)
    (hfirst : truncatedCoefficientAlgebra (fun i => ρ.restrict (f i)) (p ^ e) = ⊤)
    (hsecond : coefficientAlgebra
      (fun i => (σ.restrict (f i)).frobeniusPower p e) = ⊤) :
    (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  apply isIrreducible_of_coefficientAlgebra_eq_top (ρ.tensor (σ.frobeniusPower p e)) f
  have h := coefficientAlgebra_tensor_frobeniusPower_eq_top
    (fun i => ρ.restrict (f i)) (fun i => σ.restrict (f i)) p e hfirst hsecond
  simpa only [frobeniusPower_restrict, tensor_restrict] using h

end Ambient

end Langlands.GroupScheme.MatrixRepresentation.AdditiveTensorIrreducibility
