/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 579, 2026-11-14: isolate the proof of M398.001 from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, prefix its
namespace with Langlands.NYLL, and prove the published Prop-valued target
with canonical algebraMap expressions in place of integerMap.
Retain the six independent universes and complete source hypotheses.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationRestriction.Statements

/-!
# Valuation-ring action and normal restriction

The exact proof of M398.001 for the published canonical-map statement.
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

/-- The valuation-ring action commutes with inclusion from the normal
intermediate field and restriction of the automorphism. -/
theorem valuationSubringAutOfUniqueExtension_integerMap_restrictNormal
    (hmiddle :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base middle)
    (htarget :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, y, z, z}
        base target)
    (σ : Gal(M/K)) (a : middle.valuationSubring) :
    valuationSubringAutOfUniqueExtension_integerMap_restrictNormalStatement
      (base := base) (middle := middle) (target := target) hmiddle htarget σ a := by
  apply Subtype.ext
  change
    σ (algebraMap L M (a : L)) =
      algebraMap L M ((σ.restrictNormal L) (a : L))
  exact (AlgEquiv.restrictNormal_commutes σ L (a : L)).symm

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
