/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions

/-!
# Target: valuation equivalence from equal valuation subrings

Modified by Worker 5264, 15 November 2026: state the source theorem M109.007
`ValuedExtension.valuation_isEquiv_of_valuationSubring_eq` of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement` to
the name, omit the proof, the source variables that the statement does not
use, the universes `u v` and the rest of the source file, import the
published `Complete.Definitions` module instead of the source `Extensions`
module, and turn off the unused-variable linter for the hypothesis `hsub`,
which the proposition does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Mathlib's uniqueness criterion for valuations is expressed through
`Valuation.IsEquiv`: two valuations on the same field are equivalent exactly
when they have the same valuation subring.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {L : Type w} [Field L]

section Comparison

variable (target : CompleteDVF.{w, x} L)

set_option linter.unusedVariables false in
/-- Target: equality of valuation subrings implies valuation equivalence. -/
def valuation_isEquiv_of_valuationSubring_eqStatement
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) : Prop :=
    target.valuation.IsEquiv v'

end Comparison

end ValuedExtension
end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
