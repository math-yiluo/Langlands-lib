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
import Mathlib.RingTheory.Adjoin.Basic

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

def valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoinStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a z : target.valuationSubring} {n : ℕ} {sigma : Gal(L/K)}
    (ha : valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n)
    (hz : z ∈ Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring)),
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma z - z ∈
      target.maximalIdeal ^ n

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
