import Langlands.Global.Factors.CuspidalSplitCentreUnitaryStatement
import Langlands.Global.HeckeCharacterPositiveRealUnitary
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-!
# Proof: cuspidal realizations trivial on `A_GL` have unitary central characters

This module proves `CuspidalSplitCentreUnitaryCentralCharacterStatement`. The central
character `χ` of an actual cuspidal realization `T` exists because `T` is irreducible. If `T` is
trivial on `A_(GL_{r+1})`, then evaluating a function of `T` that does not vanish at some point
shows that `χ` is trivial on the positive real ideles `A_(G_m)`, and such a character is unitary
(`HeckeCharacter.isUnitary_of_positiveRealIdeles`). See the paired Markdown.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global

open NumberField
open scoped NNReal
open Automorphic (CuspidalOperatorRealization OperatorRealization centralIdeleCharacter)

namespace CuspidalPairPoles

/-- The positive real ideles `PositiveRealIdeles.full F a` lie in `A_(G_m)`: their finite
component is `1` and their component at every infinite place is the positive real `a`. -/
theorem isPositiveArchimedeanScalar_positiveRealIdeles {F : Type u} [Field F] [NumberField F]
    (a : ℝ≥0ˣ) : IsPositiveArchimedeanScalar (PositiveRealIdeles.full F a) :=
  ⟨rfl, ((a : ℝ≥0) : ℝ), NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero),
    fun v => PositiveRealIdeles.extensionEmbedding_full F v a⟩

end CuspidalPairPoles

/-- **Triviality on `A_GL` gives a unitary central character.** -/
theorem cuspidalSplitCentreUnitaryCentralCharacter :
    CuspidalSplitCentreUnitaryCentralCharacterStatement.{u} := by
  intro F _ _ _ r T hT
  obtain ⟨χ, hχ, -⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨f₀, x₀, h0⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  refine ⟨χ, HeckeCharacter.isUnitary_of_positiveRealIdeles χ fun a => ?_, hχ⟩
  have h1 := T.realization.centralCharacter_evaluate χ hχ f₀ (PositiveRealIdeles.full F a) x₀
  rw [hT _ (CuspidalPairPoles.isPositiveArchimedeanScalar_positiveRealIdeles a) f₀ x₀] at h1
  have h2 : ((centralIdeleCharacter F χ (PositiveRealIdeles.full F a) : ℂˣ) : ℂ) = 1 :=
    mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
  exact Units.ext h2

end Langlands.Global
