import Langlands.Group.GL.UnipotentDoubleCoset
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Type A Weyl representatives in the special linear group -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup (toGL)
open GeneralLinear (monomialRepresentative permutation permutation_mul_diagonalUnits)
open GeneralLinear.Iwasawa (diagonalUnits)

universe u

variable {n r : ℕ} {F : Type u} [Field F]

/-- The three root matrices defining `w_(a,b)(x)` in the actual special linear group. -/
def rootWeylMatrix (a b : Fin n) (hab : a ≠ b) (x : Fˣ) : SpecialLinearGroup (Fin n) F :=
  SpecialLinearGroup.transvection hab (x : F) *
    (SpecialLinearGroup.transvection hab.symm (-(↑(x⁻¹) : F)) *
      SpecialLinearGroup.transvection hab (x : F))

/-- In columns `a` and `b` the Weyl matrix has units `-x⁻¹` and `x`, respectively. -/
theorem toGL_rootWeylMatrix (a b : Fin n) (hab : a ≠ b) (x : Fˣ) :
    toGL (rootWeylMatrix a b hab x) =
      monomialRepresentative (Equiv.swap a b)
        (fun j => if j = a then -x⁻¹ else if j = b then x else 1) := by
  apply Units.ext
  ext i j
  change (Matrix.transvection a b (x : F) *
    (Matrix.transvection b a (-(↑(x⁻¹) : F)) * Matrix.transvection a b (x : F))) i j =
      monomialRepresentative (Equiv.swap a b)
        (fun j => if j = a then -x⁻¹ else if j = b then x else 1) i j
  rw [GeneralLinear.monomialRepresentative_entry]
  by_cases hia : i = a
  · subst i
    rw [Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_of_ne b a a j hab,
      Matrix.transvection_mul_apply_same]
    rcases eq_or_ne j a with rfl | hja
    · simp [Matrix.transvection, hab, hab.symm]
    · rcases eq_or_ne j b with rfl | hjb
      · simp [Matrix.transvection, hab, hab.symm]
      · simp [Matrix.transvection, hab, hja,
          hja.symm, hjb, hjb.symm, Equiv.swap_apply_of_ne_of_ne]
  · by_cases hib : i = b
    · subst i
      rw [Matrix.transvection_mul_apply_of_ne a b b j hab.symm,
        Matrix.transvection_mul_apply_same]
      rcases eq_or_ne j a with rfl | hja
      · simp [Matrix.transvection, hab, hab.symm]
      · rcases eq_or_ne j b with rfl | hjb
        · simp [Matrix.transvection, hab]
        · simp [Matrix.transvection, hab, hja, hja.symm, hjb, hjb.symm,
            Equiv.swap_apply_of_ne_of_ne]
    · rw [Matrix.transvection_mul_apply_of_ne a b i j hia,
        Matrix.transvection_mul_apply_of_ne b a i j hib]
      simp only [Matrix.transvection, Matrix.add_apply,
        Matrix.single_apply_of_row_ne (Ne.symm hia), add_zero, Matrix.one_apply]
      rcases eq_or_ne j a with rfl | hja
      · simp [hia, Ne.symm hib]
      · rcases eq_or_ne j b with rfl | hjb
        · simp [hib, Ne.symm hia]
        · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
          simp [hja, hjb, eq_comm]

/-- Composition of monomial matrices multiplies the column units after the second permutation
has acted on the columns of the first matrix. -/
theorem mul_monomialRepresentative (w v : Equiv.Perm (Fin n)) (d e : Fin n → Fˣ) :
    monomialRepresentative w d * monomialRepresentative v e =
      monomialRepresentative (w * v) ((fun j => d (v j)) * e) := by
  have hmove : diagonalUnits d * permutation n F v =
      permutation n F v * diagonalUnits (fun j => d (v j)) := by
    rw [permutation_mul_diagonalUnits]
    simp
  rw [monomialRepresentative, monomialRepresentative, monomialRepresentative, map_mul, map_mul]
  calc
    _ = permutation n F w * (diagonalUnits d * permutation n F v) * diagonalUnits e := by
      simp only [mul_assoc]
    _ = _ := by rw [hmove]; simp only [mul_assoc]

/-- `w_(a,b)(x) w_(a,b)(-1)` is the coroot diagonal with entries `x` and `x⁻¹`. -/
theorem toGL_rootWeylMatrix_mul_negOne (a b : Fin n) (hab : a ≠ b) (x : Fˣ) :
    toGL (rootWeylMatrix a b hab x * rootWeylMatrix a b hab (-1)) =
      diagonalUnits (fun j => if j = a then x else if j = b then x⁻¹ else 1) := by
  rw [map_mul, toGL_rootWeylMatrix, toGL_rootWeylMatrix, mul_monomialRepresentative,
    Equiv.swap_mul_self]
  rw [monomialRepresentative, map_one, one_mul]
  congr 1
  funext j
  rcases eq_or_ne j a with rfl | hja
  · simp [hab.symm]
  · rcases eq_or_ne j b with rfl | hjb
    · simp [hab.symm]
    · simp [hja, hjb, Equiv.swap_apply_of_ne_of_ne]

/-- The simple reflection in adjacent positions. -/
def simpleSwap (i : Fin r) : Equiv.Perm (Fin (r + 1)) := Equiv.swap i.castSucc i.succ

/-- The Banks–Levy–Sepanski matrix for the simple reflection, with sign `-1` in the upper
off-diagonal position of its adjacent block. -/
def simpleWeylMatrix (i : Fin r) : SpecialLinearGroup (Fin (r + 1)) F :=
  rootWeylMatrix i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne (-1)

theorem toGL_simpleWeylMatrix (i : Fin r) :
    toGL (simpleWeylMatrix (F := F) i) =
      monomialRepresentative (simpleSwap i)
        (fun j => if j = i.succ then (-1 : Fˣ) else 1) := by
  rw [simpleWeylMatrix, toGL_rootWeylMatrix, simpleSwap]
  congr 1
  funext j
  by_cases h : j = i.castSucc
  · subst j
    simp [(Fin.castSucc_lt_succ (i := i)).ne]
  · simp [h]

private theorem exists_simpleWord (w : Equiv.Perm (Fin (r + 1))) :
    ∃ z : List (Fin r), (z.map simpleSwap).prod = w := by
  have hm : w ∈ Submonoid.closure (Set.range (simpleSwap (r := r))) := by
    change w ∈ Submonoid.closure (Set.range fun i : Fin r => Equiv.swap i.castSucc i.succ)
    rw [Equiv.Perm.mclosure_swap_castSucc_succ r]
    exact Submonoid.mem_top _
  rw [← FreeMonoid.mrange_lift] at hm
  obtain ⟨z, hz⟩ := hm
  exact ⟨FreeMonoid.toList z, (FreeMonoid.lift_apply _ _).symm.trans hz⟩

private theorem exists_simpleWord_length (w : Equiv.Perm (Fin (r + 1))) :
    ∃ k, ∃ z : List (Fin r), (z.map simpleSwap).prod = w ∧ z.length = k := by
  obtain ⟨z, hz⟩ := exists_simpleWord w
  exact ⟨z.length, z, hz, rfl⟩

/-- A word of minimal length in the adjacent simple reflections for `w`. -/
noncomputable def weylReducedWord (w : Equiv.Perm (Fin (r + 1))) : List (Fin r) := by
  classical
  exact (Nat.find_spec (exists_simpleWord_length w)).choose

theorem weylReducedWord_prod (w : Equiv.Perm (Fin (r + 1))) :
    ((weylReducedWord w).map simpleSwap).prod = w := by
  classical
  exact (Nat.find_spec (exists_simpleWord_length w)).choose_spec.1

theorem weylReducedWord_length_le {w : Equiv.Perm (Fin (r + 1))} {z : List (Fin r)}
    (hz : (z.map simpleSwap).prod = w) : (weylReducedWord w).length ≤ z.length := by
  classical
  rw [weylReducedWord, (Nat.find_spec (exists_simpleWord_length w)).choose_spec.2]
  exact Nat.find_min' (exists_simpleWord_length w) ⟨z, hz, rfl⟩

@[simp]
theorem weylReducedWord_one : weylReducedWord (1 : Equiv.Perm (Fin (r + 1))) = [] := by
  apply List.length_eq_zero_iff.mp
  exact Nat.eq_zero_of_le_zero (weylReducedWord_length_le (z := []) rfl)

private theorem simpleWeylWord_monomial (z : List (Fin r)) :
    ∃ d : Fin (r + 1) → Fˣ,
      toGL ((z.map simpleWeylMatrix).prod) =
        monomialRepresentative (z.map simpleSwap).prod d := by
  induction z with
  | nil =>
    exact ⟨1, by simp [monomialRepresentative]⟩
  | cons i z ih =>
    obtain ⟨d, hd⟩ := ih
    simp only [List.map_cons, List.prod_cons, map_mul, hd, toGL_simpleWeylMatrix,
      mul_monomialRepresentative]
    exact ⟨_, rfl⟩

/-- The special linear representative given by multiplying the simple matrices in a chosen
minimal expression of the permutation. -/
noncomputable def weylMatrix (w : Equiv.Perm (Fin (r + 1))) :
    SpecialLinearGroup (Fin (r + 1)) F :=
  ((weylReducedWord w).map simpleWeylMatrix).prod

@[simp]
theorem weylMatrix_one : weylMatrix (F := F) (1 : Equiv.Perm (Fin (r + 1))) = 1 := by
  simp [weylMatrix]

theorem weylMatrix_monomial (w : Equiv.Perm (Fin (r + 1))) :
    ∃ d : Fin (r + 1) → Fˣ, toGL (weylMatrix w) = monomialRepresentative w d := by
  simpa only [weylMatrix, weylReducedWord_prod] using
    (simpleWeylWord_monomial (F := F) (weylReducedWord w))

end Langlands.KazhdanPatterson
