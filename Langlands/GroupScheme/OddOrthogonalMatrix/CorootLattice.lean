import Langlands.GroupScheme.OddOrthogonalMatrix.SignedCoroots
import Langlands.LinearAlgebra.TypeDParityLattice

/-! # The integral coroot lattice of the split odd group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] [Nontrivial l] {K : Type u} [Field K]

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)

/-- The actual coroot lattice is the integral lattice of even coordinate sum. -/
theorem map_corootSpan_eq_pairLattice {J : Type u}
    {P : RootDatum J (characterLattice 𝔗) (cocharacterLattice 𝔗)}
    (hP : IsRootDatumOf (identityTorus l K) P) :
    (P.corootSpan ℤ).map (GeneralLinear.cocharacterCoordEquiv l K).toLinearMap =
      TypeDParityLattice.pairLattice l := by
  have : AddMonoidHomClass (cocharacterLattice 𝔗 ≃ₗ[ℤ] (l → ℤ)) (cocharacterLattice 𝔗) (l → ℤ) :=
    SemilinearMapClass.instAddMonoidHomClass _
  change (Submodule.span ℤ (Set.range P.coroot)).map _ = _
  rw [Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    change GeneralLinear.cocharacterCoordEquiv l K (P.coroot r) ∈ TypeDParityLattice.pairLattice l
    rcases root_coroot_coordinates hP r with ⟨a, _, hr⟩ | ⟨a, b, _, _, hr⟩
    · rw [hr, map_nsmul, cocharacterCoord_signedCocharacter,
        TypeDParityLattice.pairLattice_eq_ker_sumParity]
      change TypeDParityLattice.sumParity l (2 • SymplecticMatrix.weightCoord l a) = 0
      rw [map_nsmul]
      rcases a with a | a <;> simp only [SymplecticMatrix.weightCoord_inl,
        SymplecticMatrix.weightCoord_inr, TypeDParityLattice.sumParity_single]
      all_goals decide
    · rw [hr, map_sub, cocharacterCoord_signedCocharacter, cocharacterCoord_signedCocharacter,
        TypeDParityLattice.pairLattice_eq_ker_sumParity]
      change TypeDParityLattice.sumParity l
        (SymplecticMatrix.weightCoord l a - SymplecticMatrix.weightCoord l b) = 0
      rw [map_sub]
      rcases a with a | a <;> rcases b with b | b <;>
        simp only [SymplecticMatrix.weightCoord_inl, SymplecticMatrix.weightCoord_inr,
          TypeDParityLattice.sumParity_single]
      all_goals decide
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, b, hab, rfl | rfl⟩
    · obtain ⟨r, hr⟩ : basisCharacter l K a + basisCharacter l K b ∈ Set.range P.root := by
        rw [hP.2.1, roots_identityTorus]
        exact basisCharacter_add_mem_roots hab
      apply Submodule.subset_span
      refine ⟨r, ?_⟩
      change GeneralLinear.cocharacterCoordEquiv l K (P.coroot r) = _
      rw [coroot_of_basisCharacter_add hP hab hr, map_add,
        cocharacterCoord_basisCocharacter, cocharacterCoord_basisCocharacter]
    · obtain ⟨r, hr⟩ : basisCharacter l K a - basisCharacter l K b ∈ Set.range P.root := by
        rw [hP.2.1, roots_identityTorus]
        exact basisCharacter_sub_mem_roots hab
      apply Submodule.subset_span
      refine ⟨r, ?_⟩
      change GeneralLinear.cocharacterCoordEquiv l K (P.coroot r) = _
      rw [coroot_of_basisCharacter_sub hP hab hr, map_sub,
        cocharacterCoord_basisCocharacter, cocharacterCoord_basisCocharacter]

/-- The full cocharacter lattice modulo the actual coroots is `ℤ/2ℤ`. -/
def corootQuotientEquiv {J : Type u}
    {P : RootDatum J (characterLattice 𝔗) (cocharacterLattice 𝔗)}
    (hP : IsRootDatumOf (identityTorus l K) P) :
    (cocharacterLattice 𝔗 ⧸ P.corootSpan ℤ) ≃ₗ[ℤ] ZMod 2 :=
  (Submodule.Quotient.equiv (P.corootSpan ℤ) (TypeDParityLattice.pairLattice l)
    (GeneralLinear.cocharacterCoordEquiv l K) (map_corootSpan_eq_pairLattice hP)).trans
      TypeDParityLattice.quotientEquiv

/-- The exact integral cocharacter index of the actual split odd datum. -/
theorem card_corootQuotient {J : Type u}
    {P : RootDatum J (characterLattice 𝔗) (cocharacterLattice 𝔗)}
    (hP : IsRootDatumOf (identityTorus l K) P) :
    Nat.card (cocharacterLattice 𝔗 ⧸ P.corootSpan ℤ) = 2 := by
  rw [Nat.card_congr (corootQuotientEquiv hP).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end Langlands.GroupScheme.OddOrthogonalMatrix
