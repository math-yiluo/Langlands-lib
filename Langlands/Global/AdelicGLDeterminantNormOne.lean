import Langlands.Global.AdelicGroupNormOne
import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.AdelicGroupPointTopology
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters
import Langlands.Analysis.Local.QuotientMeasureEquiv

/-! # Norm-one points of the general linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The kernel of the normalized idelic determinant on the matrix group. -/
abbrev AdelicGL.determinantNormOne : Subgroup (AdelicGL F n) :=
  (AdelicBlockDeterminantCharacter.determinantNorm F n).toMonoidHom.ker

namespace GeneralLinearGroupPoints

open AdelicGroupPoints

local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

private theorem character_matrix (χ : AlgebraicCharacter F GLₙ) (x : AdelicGroupPoints F GLₙ) :
    character F GLₙ χ x =
      GroupScheme.GeneralLinear.characterOnAffineMatrices χ (CommAlgCat.of F (Adeles F))
        (adelicHomeomorph F n x) := by
  rw [GroupScheme.GeneralLinear.characterOnAffineMatrices_apply]
  let A := CommAlgCat.of F (Adeles F)
  let e := GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F) A
  change Gm.affineUnitsEquiv (CommRingCat.of F) A (x ≫ χ.hom.hom) =
    Gm.affineUnitsEquiv (CommRingCat.of F) A (e.symm (e x) ≫ χ.hom.hom)
  rw [e.symm_apply_apply]

/-- Under the matrix homeomorphism, the intersection of all algebraic
character-norm kernels is the kernel of the determinant norm. -/
theorem mem_normOneSubgroup_iff_determinantNorm (x : AdelicGroupPoints F GLₙ) :
    x ∈ normOneSubgroup F GLₙ ↔
      adelicHomeomorph F n x ∈ AdelicGL.determinantNormOne F n := by
  let D := GroupScheme.GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of F)
  rw [mem_normOneSubgroup]
  change (∀ χ : AlgebraicCharacter F GLₙ,
    IdeleAbsoluteValue.full F (character F GLₙ χ x) = 1) ↔
      IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det (adelicHomeomorph F n x)) = 1
  constructor
  · intro h
    have hd := h D.toMul
    rw [character_matrix, GroupScheme.GeneralLinear.characterOnAffineMatrices_determinantCharacter] at hd
    exact hd
  · intro h χ
    obtain ⟨m, hm⟩ := GroupScheme.GeneralLinear.rationalCharacter_eq_zsmul_determinant
      (Additive.ofMul χ)
    have he : χ = (m • D).toMul := congrArg Additive.toMul hm
    rw [he, character_matrix, GroupScheme.GeneralLinear.characterOnAffineMatrices_zsmul,
      GroupScheme.GeneralLinear.characterOnAffineMatrices_determinantCharacter, map_zpow, h,
      one_zpow]

/-- The actual norm-one point group with its original topology is the
determinant-norm-one matrix subgroup. -/
def normOneAdelicHomeomorph :
    normOneSubgroup F GLₙ ≃ₜ* AdelicGL.determinantNormOne F n :=
  Langlands.QuotientIntegration.subgroupContinuousMulEquiv
    (adelicHomeomorph F n) _ _ fun x => (mem_normOneSubgroup_iff_determinantNorm F n x).symm

@[simp]
theorem normOneAdelicHomeomorph_val (x : normOneSubgroup F GLₙ) :
    (normOneAdelicHomeomorph F n x).val = adelicHomeomorph F n x.val := rfl

end GeneralLinearGroupPoints

end Langlands.Global
