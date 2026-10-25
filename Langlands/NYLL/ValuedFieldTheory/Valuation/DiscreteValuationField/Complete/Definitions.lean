/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 384, 2026-10-25: extract only the structural definitions
M107.001 and M107.006 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL and replace the three NYLL imports by the two Mathlib
imports supplying the fields. The retained license and notices are in
licenses/NYLL/.
-/

import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Complete discrete valuation predicate and chosen bundle

This module extracts the two structural declarations from
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`.
Completeness is the supplied maximal-ideal adic completeness of the actual
valuation subring.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

noncomputable section

universe u v

namespace Valuation

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- A complete discrete valuation. -/
class IsCompleteDiscrete (val : _root_.Valuation K Gamma) : Prop where
  /-- A complete discrete valuation has discrete rank one. -/
  [isRankOneDiscrete : val.IsRankOneDiscrete]
  /-- The valuation ring is complete for its maximal-ideal adic topology. -/
  isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring

attribute [instance] IsCompleteDiscrete.isRankOneDiscrete

end Valuation

/-- A field with a chosen complete rank-one discrete valuation. -/
structure CompleteDVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group. -/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group. -/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field. -/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation is complete and discretely rank one. -/
  [instCompleteDiscrete : Valuation.IsCompleteDiscrete valuation]

attribute [instance] CompleteDVF.instValueGroup CompleteDVF.instCompleteDiscrete

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
