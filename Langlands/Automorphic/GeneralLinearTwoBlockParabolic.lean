import Langlands.Automorphic.GroupSchemeDynamicParabolicRadical
import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Proper two-block parabolics and their canonical radical images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear

variable {a b n : ℕ} (h : a + b = n)

private def lowerTwoBlockMatrix {A : Type*} [CommRing A]
    (X : Matrix (Fin b) (Fin a) A) : Langlands.GeneralLinear n A :=
  reindex (finSumFinEquiv.trans (finCongr h))
    { val := Matrix.fromBlocks 1 0 X 1
      inv := Matrix.fromBlocks 1 0 (-X) 1
      val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
      inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one] }

/-- Positive block sizes give a proper subgroup on all test schemes. -/
theorem twoBlockParabolic_ne_top (R : CommRingCat.{u}) [Nontrivial R]
    (ha : 0 < a) (hb : 0 < b) :
    blockParabolic (Fin n) R (twoBlockWeight h) ≠ ⊤ := by
  let T : Over (Spec R) := Over.mk (𝟙 (Spec R))
  let : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  let g : GL (Fin n) Γ(T.left, ⊤) := lowerTwoBlockMatrix h (fun _ _ => 1)
  let x := (pointsEquiv (Fin n) R T).symm g
  intro htop
  have hx : x ∈ (blockParabolic (Fin n) R (twoBlockWeight h)).carrier T := by
    rw [htop]
    exact Subgroup.mem_top _
  have hzero := (mem_blockParabolic (twoBlockWeight h)).mp hx
    ((finSumFinEquiv.trans (finCongr h)) (Sum.inr ⟨0, hb⟩))
    ((finSumFinEquiv.trans (finCongr h)) (Sum.inl ⟨0, ha⟩))
    (by simp only [twoBlockWeight_inr, twoBlockWeight_inl]; norm_num)
  rw [show pointsEquiv (Fin n) R T x = g from
    (pointsEquiv (Fin n) R T).apply_symm_apply g] at hzero
  have hone : (1 : Γ(T.left, ⊤)) = 0 := by
    change (Matrix.reindex (finSumFinEquiv.trans (finCongr h))
      (finSumFinEquiv.trans (finCongr h)) (Matrix.fromBlocks 1 0 (fun _ _ => 1) 1))
      ((finSumFinEquiv.trans (finCongr h)) (Sum.inr ⟨0, hb⟩))
      ((finSumFinEquiv.trans (finCongr h)) (Sum.inl ⟨0, ha⟩)) = 0 at hzero
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at hzero
    exact hzero
  exact one_ne_zero hone

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.GroupScheme Langlands.GeneralLinear

variable (F : Type u) [Field F] {a b n : ℕ} (h : a + b = n)
  (ha : 0 < a) (hb : 0 < b) (hPD : ParabolicDynamicStatement.{u})

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- The actual positive two-block dynamic parabolic, proved proper on all tests. -/
def generalLinearTwoBlockProperParabolic : ProperRationalParabolic GLG :=
  ⟨dynamicParabolicFunctor hPD (isConnectedReductive_generalLinear F (Fin n))
    (GroupScheme.GeneralLinear.diagonalCocharacter (Fin n) (CommRingCat.of F)
      (twoBlockWeight h)), by
    change Dynamic.parabolic _ ≠ ⊤
    rw [GroupScheme.GeneralLinear.parabolic_diagonalCocharacter]
    exact GroupScheme.GeneralLinear.twoBlockParabolic_ne_top h (CommRingCat.of F) ha hb⟩

@[simp]
theorem generalLinearTwoBlockProperParabolic_val :
    (generalLinearTwoBlockProperParabolic F h ha hb hPD).val.val =
      GroupScheme.GeneralLinear.blockParabolic (Fin n) (CommRingCat.of F)
        (twoBlockWeight h) :=
  GroupScheme.GeneralLinear.parabolic_diagonalCocharacter _ _ _

/-- The canonical ambient radical is the original two-block subgroup on every test. -/
theorem properRationalParabolicRadicals_generalLinearTwoBlock
    (hG : IsConnectedReductive GLG) :
    properRationalParabolicRadicals hPD hG
        (generalLinearTwoBlockProperParabolic F h ha hb hPD) =
      GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F)
        (twoBlockWeight h) := by
  change rationalParabolicRadical hPD hG _ = _
  rw [rationalParabolicRadical_eq_dynamic hPD hG
    (GroupScheme.GeneralLinear.diagonalCocharacter (Fin n) (CommRingCat.of F)
      (twoBlockWeight h)) _ rfl]
  exact GroupScheme.GeneralLinear.unipotent_diagonalCocharacter _ _ _

end Langlands.Automorphic.GroupSchemeFunctions
