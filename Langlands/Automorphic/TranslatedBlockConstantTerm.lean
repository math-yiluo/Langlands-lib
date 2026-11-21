import Langlands.Automorphic.TranslatedBlockConstantTermOperators
import Langlands.Automorphic.BlockShapeConstantTermIdeleOrbit
import Langlands.Automorphic.TranslatedFunctionSpan
import Langlands.Automorphic.OperatorEquivalence

/-! # The actual operator action on sums of block-centre translates of constant terms -/

noncomputable section

universe u

open NumberField
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

attribute [local instance] translatedBlockTermRationalAddCommGroup translatedBlockTermContinuousAddCommGroup
  translatedBlockTermFiniteSmoothAddCommGroup translatedBlockTermFormsAddCommGroup
  translatedBlockTermStableAddCommGroup translatedBlockTermRealizationAddCommGroup

local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S

/-- Every vector in the translated space has finite-dimensional orbit under the block centre. -/
theorem translatedBlockTerm_isFiniteVector (v : TranslatedBlockConstantTerms F B S) :
    FiniteVectors.IsFiniteVector (translatedFunctionAction β φ) v :=
  translatedFunctionAction_isFiniteVector β φ
    (fun f => blockShapeConstantTerm_isFiniteVector F B (S.formInclusion f)) v

end Langlands.Automorphic
