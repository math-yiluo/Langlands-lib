import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Global.FiniteAdelicGL.Determinant
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Representation.Unramified.StandardHeckeSum

/-! # Actual local determinant characters and standard diagonals -/

noncomputable section
universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

open Langlands.Unramified Langlands.Unramified.MinusculeCosets

variable {F : Type uF} [Field F] [NumberField F]

/-- The actual restricted determinant character is the local Hecke character
composed with the actual local matrix determinant. -/
theorem finiteLocalDeterminant_eq_finiteComponent_det
    (χ : HeckeCharacter F) (n : ℕ) (v : FinitePlace F)
    (g : FiniteLocalGL F n v) :
    χ.finiteLocalDeterminant n v g =
      χ.finiteComponent v (Matrix.GeneralLinearGroup.det g) := by
  change χ.onIdeles
    (AdelicGL.determinant F n
      (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v g))) =
    χ.onIdeles (finiteIdeleInclusion F v (Matrix.GeneralLinearGroup.det g))
  rw [AdelicGL.determinant_ofFinite_localInclusion]

/-- Value at the chosen uniformizer of the canonical p-adic completion data. -/
def finiteUniformizerValue (χ : HeckeCharacter F) (v : FinitePlace F) : ℂˣ :=
  χ.finiteComponent v
    (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit

/-- The determinant of the standard diagonal is the indicated uniformizer power. -/
theorem finiteLocalDeterminant_standardDiagonal
    (χ : HeckeCharacter F) (v : FinitePlace F) (r : ℕ) (i : Fin (r + 2)) :
    χ.finiteLocalDeterminant (r + 1) v
        (standardDiagonal (CompletionPadic.padicField v) r i) =
      χ.finiteUniformizerValue v ^ i.val := by
  rw [finiteLocalDeterminant_eq_finiteComponent_det]
  have hd : Matrix.GeneralLinearGroup.det
      (standardDiagonal (CompletionPadic.padicField v) r i) =
      (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit ^ i.val := by
    apply Units.ext
    change Matrix.det (standardDiagonal (CompletionPadic.padicField v) r i).val = _
    rw [standardDiagonal_eq_subsetTorus, det_subsetTorus, card_initialSegment]
    rfl
  rw [hd, map_pow]
  rfl

end Langlands.Global.HeckeCharacter
