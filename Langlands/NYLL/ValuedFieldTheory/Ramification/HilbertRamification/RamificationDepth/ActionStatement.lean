/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: extract the indicated source proposition(s)
from commit fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
targets; prefix namespaces with Langlands.NYLL and use focused published
imports. Preserve source universes and hypotheses; omit proofs and attributes.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut
import Mathlib.RingTheory.DiscreteValuationRing.Basic

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

def addVal_valuationSubringAutOfUniqueExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) (a : target.valuationSubring),
    _root_.IsDiscreteValuationRing.addVal target.valuationSubring
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a) =
      _root_.IsDiscreteValuationRing.addVal target.valuationSubring a

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
