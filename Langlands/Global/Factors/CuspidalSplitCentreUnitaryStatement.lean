import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Automorphic.AssociatedFactorStatement

/-! # Cuspidal realizations trivial on `A_GL` have unitary central characters

Getz–Hahn (2024), p. 309, normalize cuspidal representations to be trivial on the split
component `A_(GL_n)` of the centre before stating Theorem 11.7.1. Other Library statements
(for example the archimedean component statements of
`Langlands.Automorphic.CuspidalArchimedeanComponentStatement`, and the unitarizability theorem
`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`) assume instead that
the central character is unitary. This module states the implication between the two
hypotheses for actual cuspidal realizations:

* `CuspidalSplitCentreUnitaryCentralCharacterStatement`: an actual cuspidal realization of
  `GL_{r+1}` over a number field that is trivial on `A_(GL_{r+1})`
  (`CuspidalPairPoles.IsTrivialOnSplitCentre`) has a unitary central character
  (`HasUnitaryCentralCharacter`).

This is a statement, not a proof.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization)

/-- **Triviality on `A_GL` gives a unitary central character.** Let `T` be an actual cuspidal
realization of `GL_{r+1}` over a number field `F`. If every function of `T` is invariant under
the scalar matrices `a I_{r+1}` with `a` in `A_(G_m)` (the positive reals, embedded diagonally
at the infinite places), then `T` has a central character `χ : F^× \ 𝔸_F^× → ℂ^×` with
`‖χ(x)‖ = 1` for every `x`. -/
def CuspidalSplitCentreUnitaryCentralCharacterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    CuspidalPairPoles.IsTrivialOnSplitCentre T →
      Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T

end Langlands.Global
