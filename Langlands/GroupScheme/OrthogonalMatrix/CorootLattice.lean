import Langlands.GroupScheme.OrthogonalMatrix.TypeD
import Langlands.LinearAlgebra.TypeDParityLattice

/-! # The integral coroot lattice of the split even orthogonal group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- Coordinates identify the actual integral coroot span with the type D pair lattice. -/
theorem map_corootSpan_eq_pairLattice {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (identityTorus l k) P) (hl : 3 ≤ Fintype.card l) :
    (P.corootSpan ℤ).map (GeneralLinear.cocharacterCoordEquiv l k).toLinearMap =
      TypeDParityLattice.pairLattice l := by
  let : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  change (Submodule.span ℤ (Set.range P.coroot)).map _ = _
  rw [Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨r, rfl⟩
    change GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) ∈
      TypeDParityLattice.pairLattice l
    have hr : P.root r ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
      rw [← roots_identityTorus l k, ← hP.2.1]
      exact ⟨r, rfl⟩
    obtain ⟨x, y, h₁, h₂, hxy⟩ := exists_eq_weightChar_add_of_mem_roots hr
    rw [coroot_eq_weightCochar_add hP hl h₁ h₂ hxy, map_add,
      cocharacterCoordEquiv_weightCochar, cocharacterCoordEquiv_weightCochar,
      TypeDParityLattice.pairLattice_eq_ker_sumParity]
    change TypeDParityLattice.sumParity l
      (SymplecticMatrix.weightCoord l x + SymplecticMatrix.weightCoord l y) = 0
    rw [map_add]
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [SymplecticMatrix.weightCoord_inl, SymplecticMatrix.weightCoord_inr,
        TypeDParityLattice.sumParity_single]
    all_goals decide
  · apply Submodule.span_le.mpr
    rintro v ⟨a, b, hab, rfl | rfl⟩
    · have h₁ : (Sum.inl a : l ⊕ l) ≠ Sum.inl b := by simpa using hab
      have h₂ : (Sum.inl a : l ⊕ l) ≠ (Sum.inl b : l ⊕ l).swap := by simp
      obtain ⟨r, hr⟩ : weightChar l k (Sum.inl a) + weightChar l k (Sum.inl b) ∈
          Set.range P.root := by
        rw [hP.2.1, roots_identityTorus l k]
        exact weightChar_add_mem_roots h₁ h₂
      apply Submodule.subset_span
      refine ⟨r, ?_⟩
      change GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) =
        Pi.single a 1 + Pi.single b 1
      rw [coroot_eq_weightCochar_add hP hl h₁ h₂ hr, map_add,
        cocharacterCoordEquiv_weightCochar, cocharacterCoordEquiv_weightCochar]
      rfl
    · have h₁ : (Sum.inl a : l ⊕ l) ≠ Sum.inr b := by simp
      have h₂ : (Sum.inl a : l ⊕ l) ≠ (Sum.inr b : l ⊕ l).swap := by simpa using hab
      obtain ⟨r, hr⟩ : weightChar l k (Sum.inl a) + weightChar l k (Sum.inr b) ∈
          Set.range P.root := by
        rw [hP.2.1, roots_identityTorus l k]
        exact weightChar_add_mem_roots h₁ h₂
      apply Submodule.subset_span
      refine ⟨r, ?_⟩
      change GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) =
        Pi.single a 1 - Pi.single b 1
      rw [coroot_eq_weightCochar_add hP hl h₁ h₂ hr, map_add,
        cocharacterCoordEquiv_weightCochar, cocharacterCoordEquiv_weightCochar]
      ext c
      simp [SymplecticMatrix.weightCoord_inl, SymplecticMatrix.weightCoord_inr,
        Pi.single_apply, sub_eq_add_neg]
      split_ifs <;> rfl

/-- The cocharacter lattice modulo the actual coroots is `ℤ/2ℤ`. -/
def corootQuotientEquiv {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (identityTorus l k) P) (hl : 3 ≤ Fintype.card l) :
    (cocharacterLattice 𝔻 ⧸ P.corootSpan ℤ) ≃ₗ[ℤ] ZMod 2 := by
  letI : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact (Submodule.Quotient.equiv (P.corootSpan ℤ) (TypeDParityLattice.pairLattice l)
    (GeneralLinear.cocharacterCoordEquiv l k) (map_corootSpan_eq_pairLattice hP hl)).trans
      TypeDParityLattice.quotientEquiv

theorem card_corootQuotient {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (identityTorus l k) P) (hl : 3 ≤ Fintype.card l) :
    Nat.card (cocharacterLattice 𝔻 ⧸ P.corootSpan ℤ) = 2 := by
  rw [Nat.card_congr (corootQuotientEquiv hP hl).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end Langlands.GroupScheme.OrthogonalMatrix
