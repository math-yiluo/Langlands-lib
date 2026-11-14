import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.FiniteType

/-! # Integral bases from signed spanning weights and a multiplicity bound -/

noncomputable section

namespace Langlands.GroupScheme.SignedWeightBasis

open Module Submodule
open scoped BigOperators

variable {L : Type*} [AddCommGroup L]

/-- Representatives up to sign of an additively generating support span over `ℤ`. -/
theorem span_eq_top_of_signed_support (T : Set L) (P : Finset L)
    (hT : AddSubgroup.closure T = ⊤)
    (hsign : ∀ x ∈ T, x = 0 ∨ x ∈ P ∨ -x ∈ P) :
    Submodule.span ℤ (P : Set L) = ⊤ := by
  have hclosure :
      AddSubgroup.closure T ≤ (Submodule.span ℤ (P : Set L)).toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    change x ∈ Submodule.span ℤ (P : Set L)
    rcases hsign x hx with rfl | hx | hx
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span hx
    · simpa using (Submodule.span ℤ (P : Set L)).neg_mem (Submodule.subset_span hx)
  apply top_unique
  intro x _
  exact hclosure (hT.symm ▸ AddSubgroup.mem_top x)

/-- A spanning set with positive multiplicities whose sum is at most the rank has
exactly rank-many elements, and every multiplicity is one. -/
theorem card_eq_finrank_and_multiplicity_eq_one (P : Finset L) (d : L → ℕ)
    (hspan : Submodule.span ℤ (P : Set L) = ⊤)
    (hpos : ∀ x ∈ P, 0 < d x)
    (hbound : ∑ x ∈ P, d x ≤ finrank ℤ L) :
    P.card = finrank ℤ L ∧ ∀ x ∈ P, d x = 1 := by
  have hrank : finrank ℤ L ≤ P.card := by
    have h := finrank_span_finset_le_card (R := ℤ) P
    change finrank ℤ (Submodule.span ℤ (P : Set L)) ≤ P.card at h
    rw [hspan, finrank_top] at h
    exact h
  have hcard : P.card ≤ ∑ x ∈ P, d x := by
    calc
      P.card = ∑ _x ∈ P, (1 : ℕ) := by simp
      _ ≤ ∑ x ∈ P, d x := Finset.sum_le_sum fun x hx => hpos x hx
  have heq : P.card = finrank ℤ L := le_antisymm (hcard.trans hbound) hrank
  refine ⟨heq, ?_⟩
  have hsum : (∑ _x ∈ P, (1 : ℕ)) = ∑ x ∈ P, d x := by
    simpa using le_antisymm hcard (hbound.trans hrank)
  intro x hx
  exact ((Finset.sum_eq_sum_iff_of_le fun y hy => hpos y hy).mp hsum x hx).symm

/-- The actual signed-weight representatives form an integral basis when their
positive multiplicities have total at most the integral rank. -/
def basisOfSignedSupport (T : Set L) (P : Finset L) (d : L → ℕ)
    (hT : AddSubgroup.closure T = ⊤)
    (hsign : ∀ x ∈ T, x = 0 ∨ x ∈ P ∨ -x ∈ P)
    (hpos : ∀ x ∈ P, 0 < d x)
    (hbound : ∑ x ∈ P, d x ≤ finrank ℤ L) : Basis P ℤ L :=
  finsetBasisOfTopLeSpanOfCardEqFinrank
    (span_eq_top_of_signed_support T P hT hsign).ge
    (card_eq_finrank_and_multiplicity_eq_one P d
      (span_eq_top_of_signed_support T P hT hsign) hpos hbound).1

@[simp]
theorem basisOfSignedSupport_apply (T : Set L) (P : Finset L) (d : L → ℕ)
    (hT : AddSubgroup.closure T = ⊤)
    (hsign : ∀ x ∈ T, x = 0 ∨ x ∈ P ∨ -x ∈ P)
    (hpos : ∀ x ∈ P, 0 < d x)
    (hbound : ∑ x ∈ P, d x ≤ finrank ℤ L) (x : P) :
    basisOfSignedSupport T P d hT hsign hpos hbound x = (x : L) := by
  simp [basisOfSignedSupport, finsetBasisOfTopLeSpanOfCardEqFinrank,
    coe_basisOfTopLeSpanOfCardEqFinrank]

/-- Reindex the signed-weight basis by `Fin r`, retaining the actual representatives
and the multiplicity-one conclusion. -/
theorem exists_fin_basis (T : Set L) (P : Finset L) (d : L → ℕ) (r : ℕ)
    (hT : AddSubgroup.closure T = ⊤)
    (hsign : ∀ x ∈ T, x = 0 ∨ x ∈ P ∨ -x ∈ P)
    (hpos : ∀ x ∈ P, 0 < d x)
    (hbound : ∑ x ∈ P, d x ≤ finrank ℤ L)
    (hr : finrank ℤ L = r) :
    ∃ b : Basis (Fin r) ℤ L,
      (∀ j, b j ∈ P) ∧ ∀ x ∈ P, d x = 1 := by
  obtain ⟨hcard, hmult⟩ := card_eq_finrank_and_multiplicity_eq_one P d
    (span_eq_top_of_signed_support T P hT hsign) hpos hbound
  let e : P ≃ Fin r := P.equivFinOfCardEq (hcard.trans hr)
  let b := basisOfSignedSupport T P d hT hsign hpos hbound
  refine ⟨b.reindex e, ?_, hmult⟩
  intro j
  rw [Basis.reindex_apply]
  simp [b]

/-- For a pairing that separates the second argument, vanishing on an integral
basis in the first argument detects zero in the second argument. -/
theorem eq_zero_of_basis_pairing {N : Type*} [AddCommGroup N] {ι : Type*}
    (B : L →ₗ[ℤ] N →ₗ[ℤ] ℤ)
    (hsep : ∀ y, (∀ x, B x y = 0) → y = 0)
    (b : Basis ι ℤ L) (y : N) (hy : ∀ j, B (b j) y = 0) :
    y = 0 := by
  apply hsep y
  have hf : B.flip y = 0 := b.ext fun j => hy j
  intro x
  exact LinearMap.congr_fun hf x

end Langlands.GroupScheme.SignedWeightBasis
