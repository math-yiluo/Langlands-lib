/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension.Statements

/-!
# NYLL M109.007: valuation equivalence from equal valuation subrings

Modified by Worker 5264, 15 November 2026: prove the published target
`ValuedExtension.valuation_isEquiv_of_valuationSubring_eqStatement` (M109.007)
by the source proof of `ValuedExtension.valuation_isEquiv_of_valuationSubring_eq`
in `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, keep only the section
variables of the published statement module (omitting the source's unused
`K`, its instances, and the universes `u v`), replace the source import by the
published statement module and omit the rest of the source file. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {L : Type w} [Field L]

section Comparison

variable (target : CompleteDVF.{w, x} L)

/-- Equality of valuation subrings implies valuation equivalence. -/
theorem valuation_isEquiv_of_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) :
    valuation_isEquiv_of_valuationSubring_eqStatement target v' hsub := by
  show target.valuation.IsEquiv v'
  exact (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').2 hsub

end Comparison

end ValuedExtension
end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
