/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 333, 2026-11-13, using Worker 300's compatibility route:
extract the proposition of M398.001 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, reuse the published DVF and valuation-ring action, and
replace both integerMap occurrences by their defining algebraMap expression.
Retain all six universes and the complete source hypotheses. Publish only
the Prop-valued statement. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut

/-!
# Valuation-ring action and normal restriction

The proposition of M398.001, with the canonical algebra map between the
chosen valuation rings in place of the definitionally identical integerMap.
-/

universe u v w x y z

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} {M : Type y}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsScalarTower K L M] [Normal K L]
variable {base : DVF.{u, v} K}
variable {middle : DVF.{w, x} L}
variable {target : DVF.{y, z} M}
variable [base.valuation.HasExtension middle.valuation]
variable [middle.valuation.HasExtension target.valuation]
variable [base.valuation.HasExtension target.valuation]

/-- The valuation-ring action on the image of an intermediate integral element
agrees with the image of the action of the normally restricted automorphism. -/
def valuationSubringAutOfUniqueExtension_integerMap_restrictNormalStatement
    (hmiddle :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base middle)
    (htarget :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, y, z, z}
        base target)
    (σ : Gal(M/K)) (a : middle.valuationSubring) : Prop :=
  valuationSubringAutOfUniqueExtension
        (base := base) (target := target) htarget σ
        (algebraMap middle.valuationSubring target.valuationSubring a) =
    algebraMap middle.valuationSubring target.valuationSubring
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := middle) hmiddle (σ.restrictNormal L) a)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
