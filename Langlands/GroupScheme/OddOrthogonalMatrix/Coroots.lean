import Langlands.GroupScheme.SymplecticMatrix.TypeC
import Langlands.GroupScheme.OddOrthogonalMatrix.Semisimple

/-! # Coroot coordinates of the actual odd maximal torus -/

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

/-- The positive coordinate character of the actual split torus. -/
def basisCharacter (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K]
    (a : l) : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)) :=
  SymplecticMatrix.coordChar l K a

/-- The corresponding coordinate cocharacter. -/
def basisCocharacter (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K]
    (a : l) : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)) :=
  SymplecticMatrix.coordCochar l K a

@[simp] theorem characterCoord_basisCharacter (a : l) :
    GeneralLinear.characterCoordEquiv l K (basisCharacter l K a) = Pi.single a 1 :=
  LinearEquiv.apply_symm_apply _ _

@[simp] theorem cocharacterCoord_basisCocharacter (a : l) :
    GeneralLinear.cocharacterCoordEquiv l K (basisCocharacter l K a) = Pi.single a 1 :=
  LinearEquiv.apply_symm_apply _ _

/-- Pairing with a basis character reads the integral cocharacter coordinate. -/
theorem latticePairing_basisCharacter (a : l) (ν : cocharacterLattice 𝔗) :
    latticePairing 𝔗 (basisCharacter l K a) ν = GeneralLinear.cocharacterCoordEquiv l K ν a := by
  rw [GeneralLinear.latticePairing_coord, characterCoord_basisCharacter]
  simp [Pi.single_apply]

/-- The coordinate characters are actual short roots. -/
theorem basisCharacter_mem_roots (a : l) : basisCharacter l K a ∈ roots (diagonalTorus l K) := by
  apply (mem_roots_iff _).mpr
  exact Or.inl ⟨Sum.inl a, characterCoord_basisCharacter a⟩

/-- A sum of two distinct coordinate characters is an actual long root. -/
theorem basisCharacter_add_mem_roots {a b : l} (hab : a ≠ b) :
    basisCharacter l K a + basisCharacter l K b ∈ roots (diagonalTorus l K) := by
  apply (mem_roots_iff _).mpr
  refine Or.inr ⟨Sum.inl a, Sum.inr b, hab, ?_⟩
  simp only [map_add, characterCoord_basisCharacter, SymplecticMatrix.weightCoord_inl,
    SymplecticMatrix.weightCoord_inr, Pi.single_neg, sub_neg_eq_add]

/-- A difference of two distinct coordinate characters is an actual long root. -/
theorem basisCharacter_sub_mem_roots {a b : l} (hab : a ≠ b) :
    basisCharacter l K a - basisCharacter l K b ∈ roots (diagonalTorus l K) := by
  apply (mem_roots_iff _).mpr
  exact Or.inr ⟨Sum.inl a, Sum.inl b, hab, by simp⟩

/-- Every coordinate of an actual root is zero, one or negative one. -/
theorem root_coordinate_bounds {χ : characterLattice 𝔗}
    (hχ : χ ∈ roots (diagonalTorus l K)) (c : l) :
    -1 ≤ GeneralLinear.characterCoordEquiv l K χ c ∧
      GeneralLinear.characterCoordEquiv l K χ c ≤ 1 := by
  obtain (⟨a, hc⟩ | ⟨a, b, hab, hc⟩) := (mem_roots_iff χ).mp hχ
  · rw [hc]
    rcases a with a | a <;> simp only [SymplecticMatrix.weightCoord_inl,
      SymplecticMatrix.weightCoord_inr, Pi.single_apply] <;> split_ifs <;> omega
  · rw [hc]
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [OrthogonalMatrix.index_inl, OrthogonalMatrix.index_inr] at hab <;>
      simp only [Pi.sub_apply, SymplecticMatrix.weightCoord_inl,
        SymplecticMatrix.weightCoord_inr, Pi.single_apply] <;>
      split_ifs <;> simp_all

variable {J : Type u} {P : RootDatum J
    (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)))
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)))}
    (hP : IsRootDatumOf (identityTorus l K) P)

include hP

/-- Actual roots are stable under the integral root-datum reflection. -/
theorem reflection_mem_roots (r : J) {χ : characterLattice 𝔗}
    (hχ : χ ∈ roots (diagonalTorus l K)) :
    χ - latticePairing 𝔗 χ (P.coroot r) • P.root r ∈ roots (diagonalTorus l K) := by
  obtain ⟨s, hs⟩ : χ ∈ Set.range P.root := by
    rw [hP.2.1, roots_identityTorus]
    exact hχ
  have hmem : P.root (P.reflectionPerm r s) ∈ roots (diagonalTorus l K) := by
    rw [← roots_identityTorus, ← hP.2.1]
    exact ⟨_, rfl⟩
  rw [P.root_reflectionPerm, P.reflection_apply_root, hs,
    ← P.root_coroot_eq_pairing, hP.1, hs] at hmem
  exact hmem

/-- A positive short root has twice the corresponding coordinate cocharacter. -/
theorem coroot_of_basisCharacter {r : J} {a : l} (hr : P.root r = basisCharacter l K a) :
    P.coroot r = 2 • basisCocharacter l K a := by
  let ν := GeneralLinear.cocharacterCoordEquiv l K (P.coroot r)
  have ha : ν a = 2 := by
    have h := P.pairing_same r
    rw [← P.root_coroot_eq_pairing, hP.1, hr, latticePairing_basisCharacter] at h
    exact h
  have hzero (c : l) (hca : c ≠ a) : ν c = 0 := by
    have hp := root_coordinate_bounds
      (reflection_mem_roots hP r (basisCharacter_add_mem_roots (Ne.symm hca))) a
    have hm := root_coordinate_bounds
      (reflection_mem_roots hP r (basisCharacter_sub_mem_roots hca)) a
    have hpairp : latticePairing 𝔗 (basisCharacter l K a + basisCharacter l K c) (P.coroot r) =
        ν a + ν c := by
      rw [map_add, LinearMap.add_apply, latticePairing_basisCharacter, latticePairing_basisCharacter]
    have hpairm : latticePairing 𝔗 (basisCharacter l K c - basisCharacter l K a) (P.coroot r) =
        ν c - ν a := by
      rw [map_sub, LinearMap.sub_apply, latticePairing_basisCharacter, latticePairing_basisCharacter]
    rw [hpairp, hr] at hp
    rw [hpairm, hr] at hm
    simp only [map_sub, map_add, map_zsmul, characterCoord_basisCharacter, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hca),
      smul_eq_mul] at hp hm
    omega
  apply (GeneralLinear.cocharacterCoordEquiv l K).injective
  rw [map_nsmul, cocharacterCoord_basisCocharacter]
  change ν = 2 • (Pi.single a (1 : ℤ))
  funext c
  by_cases hca : c = a
  · subst c; simpa using ha
  · simp [hzero c hca, hca]

/-- A coordinate-difference long root has the corresponding difference cocharacter. -/
theorem coroot_of_basisCharacter_sub {r : J} {a b : l} (hab : a ≠ b)
    (hr : P.root r = basisCharacter l K a - basisCharacter l K b) :
    P.coroot r = basisCocharacter l K a - basisCocharacter l K b := by
  let ν := GeneralLinear.cocharacterCoordEquiv l K (P.coroot r)
  have htwo : ν a - ν b = 2 := by
    have h := P.pairing_same r
    rw [← P.root_coroot_eq_pairing, hP.1, hr, map_sub, LinearMap.sub_apply,
      latticePairing_basisCharacter, latticePairing_basisCharacter] at h
    exact h
  have hbnda := root_coordinate_bounds (reflection_mem_roots hP r (basisCharacter_mem_roots a)) b
  have hbndb := root_coordinate_bounds (reflection_mem_roots hP r (basisCharacter_mem_roots b)) a
  rw [hr, latticePairing_basisCharacter] at hbnda hbndb
  simp only [map_sub, map_zsmul, characterCoord_basisCharacter, Pi.sub_apply,
    Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne (Ne.symm hab),
    smul_eq_mul] at hbnda hbndb
  dsimp only [ν] at htwo
  have ha : ν a = 1 := by dsimp only [ν]; omega
  have hb : ν b = -1 := by dsimp only [ν]; omega
  have hzero (c : l) (hca : c ≠ a) (hcb : c ≠ b) : ν c = 0 := by
    have hp := root_coordinate_bounds
      (reflection_mem_roots hP r (basisCharacter_add_mem_roots (Ne.symm hca))) b
    have hm := root_coordinate_bounds
      (reflection_mem_roots hP r (basisCharacter_sub_mem_roots (Ne.symm hca))) b
    have hpairp : latticePairing 𝔗 (basisCharacter l K a + basisCharacter l K c) (P.coroot r) =
        ν a + ν c := by
      rw [map_add, LinearMap.add_apply, latticePairing_basisCharacter, latticePairing_basisCharacter]
    have hpairm : latticePairing 𝔗 (basisCharacter l K a - basisCharacter l K c) (P.coroot r) =
        ν a - ν c := by
      rw [map_sub, LinearMap.sub_apply, latticePairing_basisCharacter, latticePairing_basisCharacter]
    rw [hpairp, hr] at hp
    rw [hpairm, hr] at hm
    simp only [map_sub, map_add, map_zsmul, characterCoord_basisCharacter, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab),
      Pi.single_eq_of_ne (Ne.symm hcb), smul_eq_mul] at hp hm
    omega
  apply (GeneralLinear.cocharacterCoordEquiv l K).injective
  rw [map_sub, cocharacterCoord_basisCocharacter, cocharacterCoord_basisCocharacter]
  change ν = Pi.single a 1 - Pi.single b 1
  funext c
  by_cases hca : c = a
  · subst c; simp [ha, hab]
  by_cases hcb : c = b
  · subst c; simp [hb, Ne.symm hab]
  · simp [hzero c hca hcb, hca, hcb]

end Langlands.GroupScheme.OddOrthogonalMatrix
