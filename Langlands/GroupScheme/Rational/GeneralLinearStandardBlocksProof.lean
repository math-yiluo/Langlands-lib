import Langlands.GroupScheme.Rational.GeneralLinearStandardParabolicStatement
import Langlands.GroupScheme.Rational.GeneralLinearSimpleRootsProof
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.Representation.Geometric.BlockWeylCutProof
import Langlands.Representation.Geometric.WeylUniquenessProof
import Mathlib.Order.Fin.Basic

/-! # Block comparisons for the standard subgroups of `GL_N` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear (BlockShape)
open Langlands.Geometric (blockIndex blockIndex_monotone blockIndex_eq_iff_cut_sides)

variable {N : ℕ}

/-- An adjacent pair belongs to one block precisely when its edge is uncut. -/
theorem blockIndex_adjacent_eq_iff (B : BlockShape N) (a : Fin (N - 1)) :
    blockIndex B (adjacentRootPair a).val.1 =
        blockIndex B (adjacentRootPair a).val.2 ↔ a ∉ B.cuts := by
  rw [blockIndex_eq_iff_cut_sides]
  constructor
  · intro h ha
    have hs := h a ha
    change (a.val ≤ a.val ↔ a.val + 1 ≤ a.val) at hs
    omega
  · intro ha b hb
    have hne : a.val ≠ b.val := fun h => ha (Fin.ext h ▸ hb)
    change a.val ≤ b.val ↔ a.val + 1 ≤ b.val
    omega

private theorem antitone_of_adjacent {w : Fin N → ℤ}
    (hw : ∀ a : Fin (N - 1),
      w (adjacentRootPair a).val.2 ≤ w (adjacentRootPair a).val.1) : Antitone w := by
  cases N with
  | zero => exact fun a => Fin.elim0 a
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro a
    exact hw ⟨a.val, by omega⟩

/-- The equality classes of an antitone weight vector are determined by its uncut edges. -/
theorem weight_eq_iff_blockIndex_eq (B : BlockShape N) (w : Fin N → ℤ)
    (hanti : Antitone w)
    (hedge : ∀ a : Fin (N - 1),
      w (adjacentRootPair a).val.1 = w (adjacentRootPair a).val.2 ↔ a ∉ B.cuts)
    (x y : Fin N) : w x = w y ↔ blockIndex B x = blockIndex B y := by
  constructor
  · intro hxy
    apply (blockIndex_eq_iff_cut_sides B x y).mpr
    intro a ha
    have hne : w (adjacentRootPair a).val.1 ≠ w (adjacentRootPair a).val.2 := by
      intro h
      exact ((hedge a).mp h) ha
    have hlt : w (adjacentRootPair a).val.2 < w (adjacentRootPair a).val.1 :=
      lt_of_le_of_ne (hanti (by change a.val ≤ a.val + 1; omega)) hne.symm
    constructor
    · intro hxa
      by_contra hya
      have h₁ := hanti (show x ≤ (adjacentRootPair a).val.1 from hxa)
      have h₂ := hanti (show (adjacentRootPair a).val.2 ≤ y by
        change a.val + 1 ≤ y.val; omega)
      omega
    · intro hya
      by_contra hxa
      have h₁ := hanti (show y ≤ (adjacentRootPair a).val.1 from hya)
      have h₂ := hanti (show (adjacentRootPair a).val.2 ≤ x by
        change a.val + 1 ≤ x.val; omega)
      omega
  · have hforward : ∀ m (hm : m < N) (x : Fin N), x.val ≤ m →
        blockIndex B x = blockIndex B ⟨m, hm⟩ → w x = w ⟨m, hm⟩ := by
      intro m
      induction m with
      | zero =>
        intro hm x hx _
        exact congrArg w (Fin.ext (Nat.eq_zero_of_le_zero hx))
      | succ m ih =>
        intro hm x hx hb
        by_cases hxm : x.val = m + 1
        · exact congrArg w (Fin.ext hxm)
        have hxm' : x.val ≤ m := by omega
        let a : Fin (N - 1) := ⟨m, by omega⟩
        have ha : a ∉ B.cuts := by
          intro ha
          have hs := (blockIndex_eq_iff_cut_sides B x ⟨m + 1, hm⟩).mp hb a ha
          change (x.val ≤ m ↔ m + 1 ≤ m) at hs
          omega
        have hprev : blockIndex B x = blockIndex B ⟨m, by omega⟩ := by
          apply le_antisymm
          · exact blockIndex_monotone B hxm'
          · calc
              blockIndex B ⟨m, by omega⟩ ≤ blockIndex B ⟨m + 1, hm⟩ :=
                blockIndex_monotone B (by change m ≤ m + 1; omega)
              _ = blockIndex B x := hb.symm
        exact (ih (by omega) x hxm' hprev).trans ((hedge a).mpr ha)
    intro hb
    rcases le_total x y with hxy | hyx
    · exact hforward y.val y.isLt x hxy hb
    · exact (hforward x.val x.isLt y hyx hb.symm).symm

/-- Strict weight order is the reverse strict order of block labels. -/
theorem weight_lt_iff_blockIndex_lt (B : BlockShape N) (w : Fin N → ℤ)
    (hanti : Antitone w)
    (hedge : ∀ a : Fin (N - 1),
      w (adjacentRootPair a).val.1 = w (adjacentRootPair a).val.2 ↔ a ∉ B.cuts)
    (x y : Fin N) : w x < w y ↔ blockIndex B y < blockIndex B x := by
  have heq := weight_eq_iff_blockIndex_eq B w hanti hedge
  constructor
  · intro h
    have hyx : y ≤ x := by
      by_contra hn
      have := hanti (le_of_lt (lt_of_not_ge hn))
      omega
    apply lt_of_le_of_ne (blockIndex_monotone B hyx)
    intro h'
    have := (heq y x).mpr h'
    omega
  · intro h
    have hyx : y ≤ x := by
      by_contra hn
      have := blockIndex_monotone B (le_of_lt (lt_of_not_ge hn))
      exact (not_le_of_gt h) this
    apply lt_of_le_of_ne (hanti hyx)
    intro h'
    have := (heq x y).mp h'
    exact h.ne this.symm

variable (k : Type u) [Field k]

local notation "𝔻" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))
local notation "GLdiag" => diagonalTorus (Fin N) (CommRingCat.of k)

/-- The canonical block weights have the reverse order of their block labels. -/
theorem blockShapeWeight_lt_iff_blockIndex_lt (B : BlockShape N) (x y : Fin N) :
    blockShapeWeight B x < blockShapeWeight B y ↔ blockIndex B y < blockIndex B x := by
  change -((blockIndex B x).val : ℤ) < -((blockIndex B y).val : ℤ) ↔ _
  simp only [neg_lt_neg_iff, Nat.cast_lt, Fin.lt_def]

/-- Equality of the canonical block weights is equality of the block labels. -/
theorem blockShapeWeight_eq_iff_blockIndex_eq (B : BlockShape N) (x y : Fin N) :
    blockShapeWeight B x = blockShapeWeight B y ↔ blockIndex B x = blockIndex B y := by
  change -((blockIndex B x).val : ℤ) = -((blockIndex B y).val : ℤ) ↔ _
  simp only [neg_inj, Nat.cast_inj, Fin.ext_iff]

/-- A standard cocharacter is antitone, with equality exactly at uncut adjacent edges. -/
theorem standardCocharacter_antitone_and_edges
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (B : BlockShape N) (zeta : cocharacterLattice 𝔻)
    (hzeta : IsStandardCocharacter GLdiag nu (blockSimpleRoots k B) zeta) :
    Antitone (cocharacterCoordEquiv (Fin N) k zeta) ∧
      ∀ a : Fin (N - 1),
        cocharacterCoordEquiv (Fin N) k zeta (adjacentRootPair a).val.1 =
          cocharacterCoordEquiv (Fin N) k zeta (adjacentRootPair a).val.2 ↔ a ∉ B.cuts := by
  let w := cocharacterCoordEquiv (Fin N) k zeta
  have hzero (a : Fin (N - 1)) (ha : a ∉ B.cuts) :
      w (adjacentRootPair a).val.1 = w (adjacentRootPair a).val.2 := by
    have hmem : simpleRootCharacter k a ∈ blockSimpleRoots k B := by
      rw [simpleRootCharacter_mem_blockSimpleRoots, BlockShape.mem_uncuts_iff]
      exact ha
    have h := hzeta.2.1 _ hmem
    rw [latticePairing_simpleRootCharacter] at h
    exact sub_eq_zero.mp h
  have hpos (a : Fin (N - 1)) (ha : a ∈ B.cuts) :
      w (adjacentRootPair a).val.2 < w (adjacentRootPair a).val.1 := by
    have hnot : simpleRootCharacter k a ∉ blockSimpleRoots k B := by
      rw [simpleRootCharacter_mem_blockSimpleRoots, BlockShape.mem_uncuts_iff]
      exact not_not.mpr ha
    have h := hzeta.2.2 _ (simpleRootCharacter_mem_simpleRelativeRoots k nu hnu a) hnot
    rw [latticePairing_simpleRootCharacter] at h
    exact sub_pos.mp h
  constructor
  · apply antitone_of_adjacent
    intro a
    by_cases ha : a ∈ B.cuts
    · exact (hpos a ha).le
    · exact (hzero a ha).symm.le
  · intro a
    constructor
    · intro h ha
      exact (hpos a ha).ne h.symm
    · exact hzero a

/-- Standard cocharacters and the canonical block cocharacter have identical strict orders. -/
theorem standardCocharacter_weight_lt_iff
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (B : BlockShape N) (zeta : cocharacterLattice 𝔻)
    (hzeta : IsStandardCocharacter GLdiag nu (blockSimpleRoots k B) zeta)
    (x y : Fin N) :
    cocharacterCoordEquiv (Fin N) k zeta x < cocharacterCoordEquiv (Fin N) k zeta y ↔
      blockShapeWeight B x < blockShapeWeight B y := by
  obtain ⟨hanti, hedge⟩ := standardCocharacter_antitone_and_edges k nu hnu B zeta hzeta
  rw [weight_lt_iff_blockIndex_lt B _ hanti hedge, blockShapeWeight_lt_iff_blockIndex_lt]

/-- Standard cocharacters and the canonical block cocharacter have identical equality classes. -/
theorem standardCocharacter_weight_eq_iff
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (B : BlockShape N) (zeta : cocharacterLattice 𝔻)
    (hzeta : IsStandardCocharacter GLdiag nu (blockSimpleRoots k B) zeta)
    (x y : Fin N) :
    cocharacterCoordEquiv (Fin N) k zeta x = cocharacterCoordEquiv (Fin N) k zeta y ↔
      blockShapeWeight B x = blockShapeWeight B y := by
  obtain ⟨hanti, hedge⟩ := standardCocharacter_antitone_and_edges k nu hnu B zeta hzeta
  rw [weight_eq_iff_blockIndex_eq B _ hanti hedge, blockShapeWeight_eq_iff_blockIndex_eq]

/-- The canonical block cocharacter witnesses the standard sign conditions. -/
theorem isStandardCocharacter_blockShapeWeight
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu)) (B : BlockShape N) :
    IsStandardCocharacter GLdiag nu (blockSimpleRoots k B)
      (cocharacterOfWeights k (blockShapeWeight B)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [simpleRelativeRoots_diagonalTorus k nu hnu]
    exact blockSimpleRoots_subset_range k B
  · rintro alpha ⟨a, ha, rfl⟩
    rw [latticePairing_simpleRootCharacter, cocharacterCoordEquiv_cocharacterOfWeights]
    apply sub_eq_zero.mpr
    apply (blockShapeWeight_eq_iff_blockIndex_eq B _ _).mpr
    exact (blockIndex_adjacent_eq_iff B a).mpr ((BlockShape.mem_uncuts_iff B a).mp ha)
  · intro alpha halpha hnot
    rw [simpleRelativeRoots_diagonalTorus k nu hnu] at halpha
    obtain ⟨a, rfl⟩ := halpha
    have hcut : a ∈ B.cuts := by
      simpa only [simpleRootCharacter_mem_blockSimpleRoots, BlockShape.mem_uncuts_iff,
        not_not] using hnot
    rw [latticePairing_simpleRootCharacter, cocharacterCoordEquiv_cocharacterOfWeights]
    apply sub_pos.mpr
    apply (blockShapeWeight_lt_iff_blockIndex_lt B _ _).mpr
    apply lt_of_le_of_ne (blockIndex_monotone B (by change a.val ≤ a.val + 1; omega))
    intro h
    exact ((blockIndex_adjacent_eq_iff B a).mp h) hcut

/-- Every torus cocharacter becomes its diagonal matrix cocharacter of coordinate weights. -/
theorem cocharacter_comp_diagonalTorus_eq
    (zeta : cocharacterLattice 𝔻) :
    CommGroupScheme.groupHom zeta ≫ GLdiag =
      diagonalCocharacter (Fin N) (CommRingCat.of k)
        (cocharacterCoordEquiv (Fin N) k zeta) := by
  have h := cocharacterOfWeights_comp_diagonalTorus k
    (cocharacterCoordEquiv (Fin N) k zeta)
  simpa only [cocharacterOfWeights, LinearEquiv.symm_apply_apply] using h

/-- All standard cocharacters for a block subset have the same all-test parabolic. -/
theorem parabolic_standardCocharacter
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (B : BlockShape N) (zeta : cocharacterLattice 𝔻)
    (hzeta : IsStandardCocharacter GLdiag nu (blockSimpleRoots k B) zeta) :
    Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ GLdiag) =
      blockShapeParabolic B (CommRingCat.of k) := by
  rw [cocharacter_comp_diagonalTorus_eq, parabolic_diagonalCocharacter,
    ← blockParabolic_blockShapeWeight]
  apply SubgroupFunctor.ext
  intro T
  ext g
  simp only [mem_blockParabolic, standardCocharacter_weight_lt_iff k nu hnu B zeta hzeta]

/-- All standard cocharacters for a block subset have the same all-test centralizer. -/
theorem centralizer_standardCocharacter
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (B : BlockShape N) (zeta : cocharacterLattice 𝔻)
    (hzeta : IsStandardCocharacter GLdiag nu (blockSimpleRoots k B) zeta) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ GLdiag) =
      blockShapeLevi B (CommRingCat.of k) := by
  rw [cocharacter_comp_diagonalTorus_eq, centralizer_diagonalCocharacter,
    ← blockLevi_blockShapeWeight]
  apply SubgroupFunctor.ext
  intro T
  ext g
  simp only [mem_blockLevi, ne_eq, standardCocharacter_weight_eq_iff k nu hnu B zeta hzeta]

/-- All standard cocharacters for a block subset have the same all-test unipotent subgroup. -/
theorem unipotent_standardCocharacter
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (B : BlockShape N) (zeta : cocharacterLattice 𝔻)
    (hzeta : IsStandardCocharacter GLdiag nu (blockSimpleRoots k B) zeta) :
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ GLdiag) =
      blockShapeUnipotent B (CommRingCat.of k) := by
  rw [cocharacter_comp_diagonalTorus_eq, unipotent_diagonalCocharacter,
    ← blockUnipotent_blockShapeWeight]
  apply SubgroupFunctor.ext
  intro T
  ext g
  simp only [mem_blockUnipotent, ← not_lt,
    standardCocharacter_weight_lt_iff k nu hnu B zeta hzeta]

/-- The choice-free standard parabolic is the block parabolic on every test scheme. -/
theorem standardParabolic_blockSimpleRoots
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu)) (B : BlockShape N) :
    standardParabolic GLdiag nu (blockSimpleRoots k B) =
      blockShapeParabolic B (CommRingCat.of k) := by
  apply le_antisymm
  · have hzeta := isStandardCocharacter_blockShapeWeight k nu hnu B
    have h := standardParabolic_le_dynamicParabolic GLdiag nu hzeta
    rwa [parabolic_standardCocharacter k nu hnu B _ hzeta] at h
  · intro T g hg
    apply (mem_standardParabolic GLdiag nu).mpr
    intro zeta hzeta
    rwa [parabolic_standardCocharacter k nu hnu B zeta hzeta]

/-- The choice-free standard Levi is the block Levi on every test scheme. -/
theorem standardLevi_blockSimpleRoots
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu)) (B : BlockShape N) :
    standardLevi GLdiag nu (blockSimpleRoots k B) =
      blockShapeLevi B (CommRingCat.of k) := by
  apply le_antisymm
  · have hzeta := isStandardCocharacter_blockShapeWeight k nu hnu B
    have h := standardLevi_le_dynamicCentralizer GLdiag nu hzeta
    rwa [centralizer_standardCocharacter k nu hnu B _ hzeta] at h
  · intro T g hg
    apply (mem_standardLevi GLdiag nu).mpr
    intro zeta hzeta
    rwa [centralizer_standardCocharacter k nu hnu B zeta hzeta]

/-- The choice-free standard unipotent is the block unipotent on every test scheme. -/
theorem standardUnipotent_blockSimpleRoots
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu)) (B : BlockShape N) :
    standardUnipotent GLdiag nu (blockSimpleRoots k B) =
      blockShapeUnipotent B (CommRingCat.of k) := by
  apply le_antisymm
  · have hzeta := isStandardCocharacter_blockShapeWeight k nu hnu B
    have h := standardUnipotent_le_dynamicUnipotent GLdiag nu hzeta
    rwa [unipotent_standardCocharacter k nu hnu B _ hzeta] at h
  · intro T g hg
    apply (mem_standardUnipotent GLdiag nu).mpr
    intro zeta hzeta
    rwa [unipotent_standardCocharacter k nu hnu B zeta hzeta]

end Langlands.GroupScheme.GeneralLinear
