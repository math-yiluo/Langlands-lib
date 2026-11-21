import Langlands.Group.GL.BruhatMatrixCoordinates
import Langlands.Representation.Archimedean.WhittakerCasimirEquation

/-! # The transverse and tangential parts of the Whittaker direction -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open Langlands.GeneralLinear

namespace Langlands.Archimedean

universe u

variable {F : Type u} [RCLike F] {r : ℕ}

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) F
local notation "B" => upperTriangularSubgroup (r + 1) F

/-- The projection to the genuine normal entries of the simple lower
root direction occurring in the Whittaker Casimir equation. -/
def matrixWhittakerNormalPart (w : Equiv.Perm (Fin (r + 1))) (a b : ℝ) :
    bruhatNormalSpace F w :=
  matrixEntryProjection (bruhatNormalEntry w) (matrixWhittakerLowerDirection F r a b)

theorem matrixWhittakerNormalPart_ne_zero (w : Equiv.Perm (Fin (r + 1))) (a b : ℝ)
    (hw : w ≠ Fin.revPerm) (hc : a • (1 : F) - b • (RCLike.I : F) ≠ 0) :
    matrixWhittakerNormalPart (F := F) w a b ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := exists_simple_bruhatNormalEntry w hw
  let c := a • (1 : F) - b • (RCLike.I : F)
  have he : matrixWhittakerLowerDirection F r a b i.succ i.castSucc = c := by
    rw [matrixWhittakerLowerDirection, Matrix.sum_apply, Finset.sum_eq_single i]
    · simp [c]
    · intro k _ hk
      have hne : k.succ ≠ i.succ := fun h => hk (Fin.succ_injective _ h)
      simp [Matrix.single, hne]
    · simp
  intro h
  have hz := congrArg (fun X : bruhatNormalSpace F w => X.val i.succ i.castSucc) h
  rw [matrixWhittakerNormalPart, matrixEntryProjection_apply_of_pos _ hi, he] at hz
  exact hc hz

/-- The complementary lower direction is tangent throughout the cell.
Conjugation by the upper factor can only retain a lower simple entry
at its original position. -/
theorem upperConjugation_whittakerTangent_normalEntry_eq_zero
    (w : Equiv.Perm (Fin (r + 1))) (a b : ℝ) (g : B) {i j : Fin (r + 1)}
    (hn : bruhatNormalEntry w i j) :
    ((g⁻¹ : B).val.val *
      (matrixWhittakerLowerDirection F r a b - (matrixWhittakerNormalPart (F := F) w a b).val) *
      g.val.val) i j = 0 := by
  classical
  let c := a • (1 : F) - b • (RCLike.I : F)
  let root (k : Fin r) : M := Matrix.single k.succ k.castSucc c
  let P : M →ₗ[F] bruhatNormalSpace F w := matrixEntryProjection (bruhatNormalEntry w)
  have hp (k : Fin r) : (P (root k)).val =
      if bruhatNormalEntry w k.succ k.castSucc then root k else 0 := by
    ext l m
    by_cases h : bruhatNormalEntry w k.succ k.castSucc
    · simp only [h, ↓reduceIte]
      by_cases h' : bruhatNormalEntry w l m
      · exact matrixEntryProjection_apply_of_pos _ h'
      · rw [matrixEntryProjection_apply_of_neg _ h']
        by_contra hk
        have hs : k.succ = l ∧ k.castSucc = m := by
          by_contra hs
          exact hk (by simp [root, Matrix.single, hs])
        exact h' (hs.1 ▸ hs.2 ▸ h)
    · simp only [h, ↓reduceIte]
      by_cases h' : bruhatNormalEntry w l m
      · rw [matrixEntryProjection_apply_of_pos _ h']
        by_contra hk
        have hs : k.succ = l ∧ k.castSucc = m := by
          by_contra hs
          exact hk (by simp [root, Matrix.single, hs])
        exact h (hs.1.symm ▸ hs.2.symm ▸ h')
      · exact matrixEntryProjection_apply_of_neg _ h'
  change ((g⁻¹ : B).val.val * ((∑ k : Fin r, root k) - (P (∑ k : Fin r, root k)).val) *
    g.val.val) i j = 0
  simp only [map_sum, Submodule.coe_sum, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [hp]
  by_cases hk : bruhatNormalEntry w k.succ k.castSucc
  · simp [hk]
  · simp only [hk, ↓reduceIte, sub_zero]
    let d := (g⁻¹ : B).val.val
    let e := g.val.val
    let y := d k.succ k.succ * c * e k.castSucc k.castSucc
    have hc : (d * root k * e - Matrix.single k.succ k.castSucc y).IsUpperTriangular :=
      conjugate_lowerSimple_sub_isUpperTriangular g k c
    have hs : ¬ (k.succ = i ∧ k.castSucc = j) :=
      fun h => hk (h.1.symm ▸ h.2.symm ▸ hn)
    have hy : Matrix.single k.succ k.castSucc y i j = 0 := by
      simp [Matrix.single, hs]
    have hz := hc hn.1
    rwa [Matrix.sub_apply, hy, sub_zero] at hz

end Langlands.Archimedean
