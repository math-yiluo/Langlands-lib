/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with formulation contributed by Worker 106:
extract only M304.001 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix namespaces with Langlands.NYLL and narrow imports to the published DVF
data and Mathlib valuation extensions. Preserve the five independent universes
and the predicate body. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Valuation.Extension

/-!
# Unique valuation extension for general discrete valuation fields

This module isolates the uniqueness predicate from lines 40–53 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`.
Extension compatibility of the chosen target valuation is a separate condition.
-/

universe u v w x y

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField

open Langlands.NYLL.ValuationTheory.DiscreteValuationField

namespace DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Every valuation extending the chosen base valuation is equivalent to the chosen
target valuation. This predicate does not assert that the target extends the base. -/
def HasUniqueValuationExtension (base : DVF.{u, v} K)
    (target : DVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

end DVF

end Langlands.NYLL.RamificationTheory.DiscreteValuationField
