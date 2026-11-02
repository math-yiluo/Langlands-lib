import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.Representation.Geometric.BlockShapeCutCounts

/-! Adjacent characters and block subsets for the standard diagonal torus of GL. -/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear (BlockShape)

variable {N : ℕ}

/-- The ordered pair of adjacent coordinates indexed by an interior edge. -/
def adjacentRootPair (a : Fin (N - 1)) :
    {p : Fin N × Fin N // p.1 ≠ p.2} :=
  ⟨(⟨a.val, by omega⟩, ⟨a.val + 1, by omega⟩),
    fun h => by have := congrArg Fin.val h; dsimp at this; omega⟩

theorem adjacentRootPair_injective :
    Function.Injective (adjacentRootPair (N := N)) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun p => p.val.1.val) h

variable (k : Type u) [Field k]

local notation "𝔻" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))

/-- The actual character `e_a - e_(a+1)` of the published diagonal torus. -/
def simpleRootCharacter (a : Fin (N - 1)) : characterLattice 𝔻 :=
  (characterCoordEquiv (Fin N) k).symm (rootCoord (adjacentRootPair a).val)

@[simp] theorem characterCoordEquiv_simpleRootCharacter (a : Fin (N - 1)) :
    characterCoordEquiv (Fin N) k (simpleRootCharacter k a) =
      rootCoord (adjacentRootPair a).val :=
  (characterCoordEquiv (Fin N) k).apply_symm_apply _

theorem simpleRootCharacter_injective :
    Function.Injective (simpleRootCharacter (N := N) k) := by
  intro a b h
  apply adjacentRootPair_injective
  apply rootCoord_injective
  simpa only [characterCoordEquiv_simpleRootCharacter] using
    congrArg (characterCoordEquiv (Fin N) k) h

/-- The cocharacter of the diagonal torus with the prescribed integer weights. -/
def cocharacterOfWeights (w : Fin N → ℤ) : cocharacterLattice 𝔻 :=
  (cocharacterCoordEquiv (Fin N) k).symm w

@[simp] theorem cocharacterCoordEquiv_cocharacterOfWeights (w : Fin N → ℤ) :
    cocharacterCoordEquiv (Fin N) k (cocharacterOfWeights k w) = w :=
  (cocharacterCoordEquiv (Fin N) k).apply_symm_apply _

theorem cocharacterOfWeights_comp_diagonalTorus (w : Fin N → ℤ) :
    CommGroupScheme.groupHom (cocharacterOfWeights k w) ≫
        diagonalTorus (Fin N) (CommRingCat.of k) =
      diagonalCocharacter (Fin N) (CommRingCat.of k) w := by
  exact cocharacterLatticeEquiv_symm_comp_diagonalTorus k w

theorem latticePairing_simpleRootCharacter
    (a : Fin (N - 1)) (μ : cocharacterLattice 𝔻) :
    latticePairing 𝔻 (simpleRootCharacter k a) μ =
      cocharacterCoordEquiv (Fin N) k μ (adjacentRootPair a).val.1 -
        cocharacterCoordEquiv (Fin N) k μ (adjacentRootPair a).val.2 := by
  rw [latticePairing_coord, characterCoordEquiv_simpleRootCharacter, sum_rootCoord_mul]

/-- The simple-root subset inside the blocks, defined from the actual interior edges. -/
def blockSimpleRoots (B : BlockShape N) : Set (characterLattice 𝔻) :=
  simpleRootCharacter k '' (B.uncuts : Set (Fin (N - 1)))

theorem blockSimpleRoots_subset_range (B : BlockShape N) :
    blockSimpleRoots k B ⊆ Set.range (simpleRootCharacter k) :=
  Set.image_subset_range _ _

@[simp] theorem simpleRootCharacter_mem_blockSimpleRoots
    (B : BlockShape N) (a : Fin (N - 1)) :
    simpleRootCharacter k a ∈ blockSimpleRoots k B ↔ a ∈ B.uncuts := by
  change (∃ b ∈ (B.uncuts : Set (Fin (N - 1))),
    simpleRootCharacter k b = simpleRootCharacter k a) ↔ _
  constructor
  · rintro ⟨b, hb, hab⟩
    rwa [simpleRootCharacter_injective k hab] at hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem blockSimpleRoots_injective :
    Function.Injective (blockSimpleRoots (N := N) k) := by
  intro B C h
  apply BlockShape.cuts_injective
  ext a
  have ha := congrArg (fun J => simpleRootCharacter k a ∈ J) h
  simpa only [simpleRootCharacter_mem_blockSimpleRoots, BlockShape.mem_uncuts_iff,
    eq_iff_iff, not_iff_not] using ha

/-- Every subset of the adjacent characters determines exactly one ordered block shape. -/
theorem existsUnique_blockSimpleRoots (J : Set (characterLattice 𝔻))
    (hJ : J ⊆ Set.range (simpleRootCharacter k)) :
    ∃! B : BlockShape N, blockSimpleRoots k B = J := by
  classical
  let s : Finset (Fin (N - 1)) := (simpleRootCharacter k ⁻¹' J).toFinset
  let B : BlockShape N := (BlockShape.cutEquiv N).symm (Finset.univ \ s)
  have hB : blockSimpleRoots k B = J := by
    apply Set.Subset.antisymm
    · rintro χ ⟨a, ha, rfl⟩
      have hcut : a ∉ B.cuts := (BlockShape.mem_uncuts_iff B a).mp ha
      simpa only [B, BlockShape.cuts_cutEquiv_symm, Finset.mem_sdiff, Finset.mem_univ,
        true_and, not_not, s, Set.mem_toFinset, Set.mem_preimage] using hcut
    · intro χ hχ
      obtain ⟨a, rfl⟩ := hJ hχ
      apply (simpleRootCharacter_mem_blockSimpleRoots k B a).mpr
      apply (BlockShape.mem_uncuts_iff B a).mpr
      simpa only [B, BlockShape.cuts_cutEquiv_symm, Finset.mem_sdiff, Finset.mem_univ,
        true_and, not_not, s, Set.mem_toFinset, Set.mem_preimage] using hχ
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact blockSimpleRoots_injective k (hC.trans hB.symm)

end Langlands.GroupScheme.GeneralLinear
