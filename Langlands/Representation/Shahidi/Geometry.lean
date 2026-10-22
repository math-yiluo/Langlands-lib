import Langlands.Group.GL.Maps
import Langlands.Group.GL.BlockUnipotent
import Langlands.Group.GL.RankMaps
import Mathlib.Data.Matrix.Block

/-! # Shahidi's two-block Weyl element and rectangular radicals -/

namespace Langlands.Shahidi

open GeneralLinear Matrix

universe u

variable (m n : ℕ) (R : Type u) [CommRing R]

/-- Rank transport changes only the type-level expression for the total rank. -/
def swapRank : Langlands.GeneralLinear (n + m) R ≃* Langlands.GeneralLinear (m + n) R :=
  GeneralLinear.reindex (finCongr (Nat.add_comm n m))

/-- The block permutation sends column coordinates `(n,m)` to row coordinates `(m,n)`. -/
def blockWeylPermutation : Equiv.Perm (Fin (m + n)) :=
  (finCongr (Nat.add_comm m n)).trans (finAddFlip (m := n) (n := m))

/-- Shahidi's representative `[[0_(m,n), I_m], [I_n, 0_(n,m)]]`. -/
def blockWeyl : Langlands.GeneralLinear (m + n) R :=
  GeneralLinear.permutation (m + n) R (blockWeylPermutation m n)

@[simp] theorem blockWeylPermutation_first (i : Fin n) :
    blockWeylPermutation m n (Fin.cast (Nat.add_comm n m) (i.castAdd m)) = i.natAdd m := by
  simp [blockWeylPermutation]

@[simp] theorem blockWeylPermutation_second (i : Fin m) :
    blockWeylPermutation m n (Fin.cast (Nat.add_comm n m) (i.natAdd n)) = i.castAdd n := by
  simp [blockWeylPermutation]

@[simp] theorem blockWeylPermutation_symm_first (i : Fin m) :
    (blockWeylPermutation m n).symm (i.castAdd n) =
      Fin.cast (Nat.add_comm n m) (i.natAdd n) := by
  apply (blockWeylPermutation m n).injective
  rw [Equiv.apply_symm_apply, blockWeylPermutation_second]

@[simp] theorem blockWeylPermutation_symm_second (i : Fin n) :
    (blockWeylPermutation m n).symm (i.natAdd m) =
      Fin.cast (Nat.add_comm n m) (i.castAdd m) := by
  apply (blockWeylPermutation m n).injective
  rw [Equiv.apply_symm_apply, blockWeylPermutation_first]

/-- Entry formula, with the exact all-positive permutation convention. -/
theorem blockWeyl_entry (i j : Fin (m + n)) :
    blockWeyl m n R i j = if blockWeylPermutation m n j = i then 1 else 0 :=
  GeneralLinear.permutation_entry _ _ _ _ _

@[simp] theorem blockWeyl_top_right (i j : Fin m) :
    blockWeyl m n R (i.castAdd n) (Fin.cast (Nat.add_comm n m) (j.natAdd n)) =
      if i = j then 1 else 0 := by
  rw [blockWeyl_entry, blockWeylPermutation_second]
  simp [eq_comm]

@[simp] theorem blockWeyl_bottom_left (i j : Fin n) :
    blockWeyl m n R (i.natAdd m) (Fin.cast (Nat.add_comm n m) (j.castAdd m)) =
      if i = j then 1 else 0 := by
  rw [blockWeyl_entry, blockWeylPermutation_first]
  simp [eq_comm]

@[simp] theorem blockWeyl_top_left (i : Fin m) (j : Fin n) :
    blockWeyl m n R (i.castAdd n) (Fin.cast (Nat.add_comm n m) (j.castAdd m)) = 0 := by
  rw [blockWeyl_entry, blockWeylPermutation_first, ite_eq_right]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

@[simp] theorem blockWeyl_bottom_right (i : Fin n) (j : Fin m) :
    blockWeyl m n R (i.natAdd m) (Fin.cast (Nat.add_comm n m) (j.natAdd n)) = 0 := by
  rw [blockWeyl_entry, blockWeylPermutation_second, ite_eq_right]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

/-- The actual upper radical matrix `[[I_m,a],[0,I_n]]`. -/
def upper (a : Matrix (Fin m) (Fin n) R) : Langlands.GeneralLinear (m + n) R :=
  GeneralLinear.reindex finSumFinEquiv (GeneralLinear.sumBlockUnipotent a)

@[simp] theorem upper_first_first (a : Matrix (Fin m) (Fin n) R) (i j : Fin m) :
    upper m n R a (i.castAdd n) (j.castAdd n) = if i = j then 1 else 0 := by
  change fromBlocks 1 a 0 1 (finSumFinEquiv.symm _) (finSumFinEquiv.symm _) = _
  simp [Matrix.one_apply]

@[simp] theorem upper_first_second (a : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    upper m n R a (i.castAdd n) (j.natAdd m) = a i j := by
  change fromBlocks 1 a 0 1 (finSumFinEquiv.symm _) (finSumFinEquiv.symm _) = _
  simp

@[simp] theorem upper_second_first (a : Matrix (Fin m) (Fin n) R) (i : Fin n) (j : Fin m) :
    upper m n R a (i.natAdd m) (j.castAdd n) = 0 := by
  change fromBlocks 1 a 0 1 (finSumFinEquiv.symm _) (finSumFinEquiv.symm _) = _
  simp

@[simp] theorem upper_second_second (a : Matrix (Fin m) (Fin n) R) (i j : Fin n) :
    upper m n R a (i.natAdd m) (j.natAdd m) = if i = j then 1 else 0 := by
  change fromBlocks 1 a 0 1 (finSumFinEquiv.symm _) (finSumFinEquiv.symm _) = _
  simp [Matrix.one_apply]

@[simp] theorem upper_zero : upper m n R 0 = 1 := by
  change GeneralLinear.reindex finSumFinEquiv (GeneralLinear.sumBlockUnipotent 0) = 1
  have h : GeneralLinear.sumBlockUnipotent (0 : Matrix (Fin m) (Fin n) R) = 1 := by
    apply Units.ext
    exact fromBlocks_one
  rw [h, map_one]

theorem upper_add (a b : Matrix (Fin m) (Fin n) R) :
    upper m n R (a + b) = upper m n R a * upper m n R b := by
  unfold upper
  rw [← map_mul]
  congr 1
  apply Units.ext
  simp [GeneralLinear.sumBlockUnipotent, fromBlocks_multiply, add_comm]

@[simp] theorem upper_neg (a : Matrix (Fin m) (Fin n) R) :
    upper m n R (-a) = (upper m n R a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← upper_add, neg_add_cancel, upper_zero]

theorem upper_injective : Function.Injective (upper m n R) := by
  intro a b h
  ext i j
  simpa using congrArg (fun g : Langlands.GeneralLinear (m + n) R =>
    g (i.castAdd n) (j.natAdd m)) h

/-- The additive rectangular space parametrizes an actual multiplicative subgroup. -/
def upperHom : Multiplicative (Matrix (Fin m) (Fin n) R) →*
    Langlands.GeneralLinear (m + n) R where
  toFun a := upper m n R a.toAdd
  map_one' := upper_zero m n R
  map_mul' a b := upper_add m n R a.toAdd b.toAdd

/-- Shahidi's original upper radical in its actual ambient matrix group. -/
def upperRadical : Subgroup (Langlands.GeneralLinear (m + n) R) :=
  (upperHom m n R).range

/-- `U'` is the upper radical with the block sizes exchanged, on the same total rank. -/
def intertwiningUnipotent (a : Matrix (Fin n) (Fin m) R) :
    Langlands.GeneralLinear (m + n) R :=
  swapRank m n R (upper n m R a)

/-- Rectangular coordinates for the subgroup of integration in (0.1). -/
def intertwiningHom : Multiplicative (Matrix (Fin n) (Fin m) R) →*
    Langlands.GeneralLinear (m + n) R :=
  (swapRank m n R).toMonoidHom.comp (upperHom n m R)

/-- The subgroup `U'` of the actual total-rank matrix group. -/
def intertwiningRadical : Subgroup (Langlands.GeneralLinear (m + n) R) :=
  (intertwiningHom m n R).range

theorem intertwiningUnipotent_injective :
    Function.Injective (intertwiningUnipotent m n R) :=
  (swapRank m n R).injective.comp (upper_injective n m R)

@[simp] theorem intertwiningUnipotent_zero : intertwiningUnipotent m n R 0 = 1 := by
  simp [intertwiningUnipotent]

theorem intertwiningUnipotent_add (a b : Matrix (Fin n) (Fin m) R) :
    intertwiningUnipotent m n R (a + b) =
      intertwiningUnipotent m n R a * intertwiningUnipotent m n R b := by
  simp [intertwiningUnipotent, upper_add]

@[simp] theorem intertwiningUnipotent_neg (a : Matrix (Fin n) (Fin m) R) :
    intertwiningUnipotent m n R (-a) = (intertwiningUnipotent m n R a)⁻¹ := by
  simp [intertwiningUnipotent]

/-- The opposite radical matrix obtained by the exact block Weyl conjugation. -/
def lower (a : Matrix (Fin n) (Fin m) R) : Langlands.GeneralLinear (m + n) R :=
  blockWeyl m n R * intertwiningUnipotent m n R a * (blockWeyl m n R)⁻¹

private theorem conjugate_entry (g : Langlands.GeneralLinear (n + m) R)
    (i j : Fin (m + n)) :
    (blockWeyl m n R * swapRank m n R g * (blockWeyl m n R)⁻¹) i j =
      g (Fin.cast (Nat.add_comm m n) ((blockWeylPermutation m n).symm i))
        (Fin.cast (Nat.add_comm m n) ((blockWeylPermutation m n).symm j)) := by
  rw [blockWeyl, GeneralLinear.permutation_conjugate_entry]
  rfl

@[simp] theorem lower_first_first (a : Matrix (Fin n) (Fin m) R) (i j : Fin m) :
    lower m n R a (i.castAdd n) (j.castAdd n) = if i = j then 1 else 0 := by
  simp [lower, intertwiningUnipotent, conjugate_entry]

@[simp] theorem lower_first_second (a : Matrix (Fin n) (Fin m) R) (i : Fin m) (j : Fin n) :
    lower m n R a (i.castAdd n) (j.natAdd m) = 0 := by
  simp [lower, intertwiningUnipotent, conjugate_entry]

@[simp] theorem lower_second_first (a : Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) :
    lower m n R a (i.natAdd m) (j.castAdd n) = a i j := by
  simp [lower, intertwiningUnipotent, conjugate_entry]

@[simp] theorem lower_second_second (a : Matrix (Fin n) (Fin m) R) (i j : Fin n) :
    lower m n R a (i.natAdd m) (j.natAdd m) = if i = j then 1 else 0 := by
  simp [lower, intertwiningUnipotent, conjugate_entry]

/-- The lower coordinates are the transpose of the original upper coordinates. -/
theorem lower_transpose (a : Matrix (Fin m) (Fin n) R) :
    (lower m n R a.transpose : Matrix (Fin (m + n)) (Fin (m + n)) R) =
      (upper m n R a : Matrix (Fin (m + n)) (Fin (m + n)) R).transpose := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [Matrix.transpose_apply, eq_comm]

/-- The Weyl representative exchanges the two actual diagonal Levi factors. -/
theorem blockWeyl_conjugate_blockSum
    (g : Langlands.GeneralLinear n R) (h : Langlands.GeneralLinear m R) :
    blockWeyl m n R * swapRank m n R (GeneralLinear.blockSum (g, h)) *
      (blockWeyl m n R)⁻¹ = GeneralLinear.blockSum (h, g) := by
  apply Units.ext
  ext i j
  rw [conjugate_entry]
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

private theorem continuous_upperCoordinates :
    Continuous (GeneralLinear.sumBlockUnipotent (R := R) (a := m) (b := n)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact continuous_const
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const
    · exact continuous_const
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact continuous_const
    · change Continuous (fun a : Matrix (Fin m) (Fin n) R => -(a i j))
      exact (show Continuous (fun a : Matrix (Fin m) (Fin n) R => a i j) from
        (continuous_apply j).comp (continuous_apply i)).neg
    · exact continuous_const
    · exact continuous_const

@[fun_prop] theorem continuous_upper : Continuous (upper m n R) :=
  (GeneralLinear.reindexContinuous (R := R) finSumFinEquiv).continuous.comp
    (continuous_upperCoordinates m n R)

@[fun_prop] theorem continuous_intertwiningUnipotent :
    Continuous (intertwiningUnipotent m n R) :=
  (GeneralLinear.reindexContinuous (R := R) (finCongr (Nat.add_comm n m))).continuous.comp
    (continuous_upper n m R)

@[fun_prop] theorem continuous_lower : Continuous (lower m n R) :=
  (continuous_const.mul (continuous_intertwiningUnipotent m n R)).mul continuous_const

end Topology

end Langlands.Shahidi
