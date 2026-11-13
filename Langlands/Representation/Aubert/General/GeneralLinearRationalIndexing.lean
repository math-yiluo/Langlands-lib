import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Aubert.RootSubsetExpansion
import Langlands.GroupScheme.Rational.GeneralLinearStandardParabolicProof
import Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer

/-! # Actual GL simple-root indexing for the rational-point Aubert family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GroupScheme
open Langlands.GeneralLinear (BlockShape)

variable (k : Type u) [Field k] (N : ℕ)

/-- The decreasing integral cocharacter that selects the upper triangular chamber. -/
def upperCocharacter :
    cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))) :=
  GroupScheme.GeneralLinear.cocharacterOfWeights k (fun a => -(a.val : ℤ))

theorem upperCocharacter_strictAnti :
    StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) k
      (upperCocharacter k N)) := by
  rw [upperCocharacter, GroupScheme.GeneralLinear.cocharacterCoordEquiv_cocharacterOfWeights]
  intro a b hab
  exact neg_lt_neg (Int.ofNat_lt.mpr hab)

theorem upperCocharacter_generic :
    IsGenericCocharacter
      (GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k))
      (upperCocharacter k N) :=
  (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff k _).mpr
    (upperCocharacter_strictAnti k N).injective

variable {N}
  (ν : cocharacterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))))
  (hν : StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) k ν))

local notation "iD" => GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k)

/-- Each interior edge is its actual adjacent simple character, with its root proof. -/
def edgeSimpleRootEquiv : Fin (N - 1) ≃ SimpleRoot iD ν :=
  Equiv.ofBijective
    (fun a => ⟨GroupScheme.GeneralLinear.simpleRootCharacter k a,
      GroupScheme.GeneralLinear.simpleRootCharacter_mem_simpleRelativeRoots k ν hν a⟩)
    ⟨fun _ _ h => GroupScheme.GeneralLinear.simpleRootCharacter_injective k
      (congrArg Subtype.val h), by
      intro α
      have hα : (α : characterLattice _) ∈
          Set.range (GroupScheme.GeneralLinear.simpleRootCharacter k (N := N)) := by
        simpa only [GroupScheme.GeneralLinear.simpleRelativeRoots_diagonalTorus k ν hν]
          using α.property
      obtain ⟨a, ha⟩ := hα
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem edgeSimpleRootEquiv_val (a : Fin (N - 1)) :
    (edgeSimpleRootEquiv k ν hν a : characterLattice _) =
      GroupScheme.GeneralLinear.simpleRootCharacter k a := rfl

/-- The existing block-root equivalence, now valued in actual simple-root subsets. -/
def blockRootSubsetEquiv : BlockShape N ≃ Finset (SimpleRoot iD ν) :=
  (BlockShape.leviRootSubsetEquiv N).trans (edgeSimpleRootEquiv k ν hν).finsetCongr

@[simp] theorem blockRootSubsetEquiv_apply (B : BlockShape N) :
    blockRootSubsetEquiv k ν hν B = B.uncuts.map (edgeSimpleRootEquiv k ν hν).toEmbedding :=
  rfl

@[simp] theorem blockRootSubsetEquiv_card (B : BlockShape N) :
    (blockRootSubsetEquiv k ν hν B).card = N - B.length := by
  rw [blockRootSubsetEquiv_apply, Finset.card_map, BlockShape.uncuts_card]

/-- The actual root set is the published set of adjacent characters inside the blocks. -/
theorem rootSet_blockRootSubsetEquiv (B : BlockShape N) :
    rootSet iD ν (blockRootSubsetEquiv k ν hν B) =
      GroupScheme.GeneralLinear.blockSimpleRoots k B := by
  ext χ
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [blockRootSubsetEquiv_apply] at hα
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hα
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨edgeSimpleRootEquiv k ν hν a,
      Finset.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩

/-- The unadjusted general sign is the existing GL block sign in every rank. -/
theorem blockRootSubsetEquiv_sign (B : BlockShape N) :
    (-1 : ℤ) ^ (blockRootSubsetEquiv k ν hν B).card =
      (-1 : ℤ) ^ (N - B.length) := by
  rw [blockRootSubsetEquiv_card]

/-- Standard rational parabolics are the canonical inverse images of matrix parabolics. -/
theorem parabolic_blockRootSubsetEquiv (B : BlockShape N) :
    parabolic iD ν (blockRootSubsetEquiv k ν hν B) =
      (B.parabolic k).comap
        (GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of k)).toMonoidHom := by
  change standardParabolicPoints iD ν _ = _
  rw [rootSet_blockRootSubsetEquiv]
  change (standardParabolic iD ν _).carrier _ = _
  rw [GroupScheme.GeneralLinear.standardParabolic_blockSimpleRoots k ν hν B]
  rw [GroupScheme.GeneralLinear.blockShapeParabolicPoints_eq_comap,
    ← GroupScheme.GeneralLinear.rationalPointsEquiv_toMonoidHom]

/-- Standard rational Levis are the canonical inverse images of embedded matrix Levis. -/
theorem levi_blockRootSubsetEquiv (B : BlockShape N) :
    levi iD ν (blockRootSubsetEquiv k ν hν B) =
      (B.leviSubgroup k).comap
        (GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of k)).toMonoidHom := by
  change standardLeviPoints iD ν _ = _
  rw [rootSet_blockRootSubsetEquiv]
  change (standardLevi iD ν _).carrier _ = _
  rw [GroupScheme.GeneralLinear.standardLevi_blockSimpleRoots k ν hν B]
  rw [GroupScheme.GeneralLinear.blockShapeLeviPoints_eq_comap,
    ← GroupScheme.GeneralLinear.rationalPointsEquiv_toMonoidHom]

/-- Standard rational radicals are the canonical inverse images of matrix radicals. -/
theorem unipotent_blockRootSubsetEquiv (B : BlockShape N) :
    unipotent iD ν (blockRootSubsetEquiv k ν hν B) =
      (B.unipotentSubgroup k).comap
        (GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of k)).toMonoidHom := by
  change standardUnipotentPoints iD ν _ = _
  rw [rootSet_blockRootSubsetEquiv]
  change (standardUnipotent iD ν _).carrier _ = _
  rw [GroupScheme.GeneralLinear.standardUnipotent_blockSimpleRoots k ν hν B]
  rw [GroupScheme.GeneralLinear.blockShapeUnipotentPoints_eq_comap,
    ← GroupScheme.GeneralLinear.rationalPointsEquiv_toMonoidHom]

end Langlands.Aubert.General.RationalPointFamily.GL
