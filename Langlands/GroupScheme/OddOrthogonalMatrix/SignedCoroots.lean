import Langlands.GroupScheme.OddOrthogonalMatrix.Coroots

/-! # Signed coroot coordinates for the actual odd root datum -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {K : Type u} [Field K]

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)

/-- The character of a signed coordinate. -/
def signedCharacter (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K] :
    l ⊕ l → characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)) :=
  Sum.elim (basisCharacter l K) (fun a => -basisCharacter l K a)

/-- The cocharacter of a signed coordinate. -/
def signedCocharacter (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K] :
    l ⊕ l → cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)) :=
  Sum.elim (basisCocharacter l K) (fun a => -basisCocharacter l K a)

@[simp] theorem characterCoord_signedCharacter (a : l ⊕ l) :
    GeneralLinear.characterCoordEquiv l K (signedCharacter l K a) =
      SymplecticMatrix.weightCoord l a := by
  have : AddMonoidHomClass (characterLattice 𝔗 ≃ₗ[ℤ] (l → ℤ)) (characterLattice 𝔗) (l → ℤ) :=
    SemilinearMapClass.instAddMonoidHomClass _
  cases a <;> simp [signedCharacter, Pi.single_neg]

@[simp] theorem cocharacterCoord_signedCocharacter (a : l ⊕ l) :
    GeneralLinear.cocharacterCoordEquiv l K (signedCocharacter l K a) =
      SymplecticMatrix.weightCoord l a := by
  have : AddMonoidHomClass (cocharacterLattice 𝔗 ≃ₗ[ℤ] (l → ℤ)) (cocharacterLattice 𝔗) (l → ℤ) :=
    SemilinearMapClass.instAddMonoidHomClass _
  cases a <;> simp [signedCocharacter, Pi.single_neg]

variable {J : Type u} {P : RootDatum J
    (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)))
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)))}
    (hP : IsRootDatumOf (identityTorus l K) P)

include hP

/-- Reflection in the short coordinate root gives the positive sum coroot. -/
theorem coroot_of_basisCharacter_add {r : J} {a b : l} (hab : a ≠ b)
    (hr : P.root r = basisCharacter l K a + basisCharacter l K b) :
    P.coroot r = basisCocharacter l K a + basisCocharacter l K b := by
  have : AddMonoidHomClass (cocharacterLattice 𝔗 ≃ₗ[ℤ] (l → ℤ)) (cocharacterLattice 𝔗) (l → ℤ) :=
    SemilinearMapClass.instAddMonoidHomClass _
  have hshort : basisCharacter l K b ∈ Set.range P.root := by
    rw [hP.2.1, roots_identityTorus]
    exact basisCharacter_mem_roots b
  have hlong : basisCharacter l K a - basisCharacter l K b ∈ Set.range P.root := by
    rw [hP.2.1, roots_identityTorus]
    exact basisCharacter_sub_mem_roots hab
  obtain ⟨s, hs⟩ := hshort
  obtain ⟨t, ht⟩ := hlong
  have hts : P.pairing t s = -2 := by
    rw [← P.root_coroot_eq_pairing, hP.1, ht, coroot_of_basisCharacter hP hs]
    simp [map_sub, latticePairing_basisCharacter, hab]
  have hst : P.pairing s t = -1 := by
    rw [← P.root_coroot_eq_pairing, hP.1, hs, coroot_of_basisCharacter_sub hP hab ht]
    simp [latticePairing_basisCharacter, Ne.symm hab]
  have he : P.root r = P.reflection s (P.root t) := by
    rw [P.reflection_apply_root, hts, hr, ht, hs]
    module
  rw [P.coroot_eq_coreflection_of_root_eq he, P.coreflection_apply_coroot, hst,
    coroot_of_basisCharacter_sub hP hab ht, coroot_of_basisCharacter hP hs]
  module

omit hP [DecidableEq l] in
/-- Opposite root indices have opposite coroots. -/
theorem coroot_eq_neg_of_root_eq_neg {r s : J} (h : P.root r = -P.root s) :
    P.coroot r = -P.coroot s :=
  P.coroot_eq_neg_iff.mpr (P.root_eq_neg_iff.mp h)

/-- Both signs of a short root have twice the corresponding signed cocharacter. -/
theorem coroot_of_signedCharacter {r : J} {a : l ⊕ l}
    (hr : P.root r = signedCharacter l K a) :
    P.coroot r = 2 • signedCocharacter l K a := by
  rcases a with a | a
  · exact coroot_of_basisCharacter hP hr
  · have hshort : basisCharacter l K a ∈ Set.range P.root := by
      rw [hP.2.1, roots_identityTorus]
      exact basisCharacter_mem_roots a
    obtain ⟨s, hs⟩ := hshort
    have he : P.root r = -P.root s := by simpa [signedCharacter, hs] using hr
    rw [coroot_eq_neg_of_root_eq_neg he, coroot_of_basisCharacter hP hs]
    simp [signedCocharacter]

/-- Every signed long root has the same signed coordinate cocharacter. -/
theorem coroot_of_signedCharacter_sub {r : J} {a b : l ⊕ l}
    (hab : OrthogonalMatrix.index a ≠ OrthogonalMatrix.index b)
    (hr : P.root r = signedCharacter l K a - signedCharacter l K b) :
    P.coroot r = signedCocharacter l K a - signedCocharacter l K b := by
  rcases a with a | a <;> rcases b with b | b
  · exact coroot_of_basisCharacter_sub hP hab hr
  · have he : P.root r = basisCharacter l K a + basisCharacter l K b := by
      simpa [signedCharacter] using hr
    simpa [signedCocharacter] using coroot_of_basisCharacter_add hP hab he
  · have hsum : basisCharacter l K a + basisCharacter l K b ∈ Set.range P.root := by
      rw [hP.2.1, roots_identityTorus]
      exact basisCharacter_add_mem_roots hab
    obtain ⟨s, hs⟩ := hsum
    have he : P.root r = -P.root s := by
      rw [hr, hs]
      simp [signedCharacter, neg_add_rev, sub_eq_add_neg, add_comm]
    rw [coroot_eq_neg_of_root_eq_neg he, coroot_of_basisCharacter_add hP hab hs]
    simp [signedCocharacter, sub_eq_add_neg, add_comm]
  · have he : P.root r = basisCharacter l K b - basisCharacter l K a := by
      simpa [signedCharacter, sub_eq_add_neg, add_comm] using hr
    simpa [signedCocharacter, sub_eq_add_neg, add_comm] using
      coroot_of_basisCharacter_sub hP (Ne.symm hab) he

/-- The exact root set and its corresponding coroots in integral coordinates. -/
theorem root_coroot_coordinates (r : J) :
    (∃ a : l ⊕ l, P.root r = signedCharacter l K a ∧
      P.coroot r = 2 • signedCocharacter l K a) ∨
    ∃ a b : l ⊕ l, OrthogonalMatrix.index a ≠ OrthogonalMatrix.index b ∧
      P.root r = signedCharacter l K a - signedCharacter l K b ∧
      P.coroot r = signedCocharacter l K a - signedCocharacter l K b := by
  have : AddMonoidHomClass (characterLattice 𝔗 ≃ₗ[ℤ] (l → ℤ)) (characterLattice 𝔗) (l → ℤ) :=
    SemilinearMapClass.instAddMonoidHomClass _
  have hr : P.root r ∈ roots (diagonalTorus l K) := by
    rw [← roots_identityTorus, ← hP.2.1]
    exact Set.mem_range_self r
  rcases (mem_roots_iff _).mp hr with ⟨a, ha⟩ | ⟨a, b, hab, habr⟩
  · have he : P.root r = signedCharacter l K a := by
      apply (GeneralLinear.characterCoordEquiv l K).injective
      simpa using ha
    exact Or.inl ⟨a, he, coroot_of_signedCharacter hP he⟩
  · have he : P.root r = signedCharacter l K a - signedCharacter l K b := by
      apply (GeneralLinear.characterCoordEquiv l K).injective
      simpa using habr
    exact Or.inr ⟨a, b, hab, he, coroot_of_signedCharacter_sub hP hab he⟩

end Langlands.GroupScheme.OddOrthogonalMatrix
