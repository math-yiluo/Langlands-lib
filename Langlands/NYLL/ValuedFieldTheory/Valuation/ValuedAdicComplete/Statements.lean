/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 449 (2026-10-25): extract only the statements of
M247.002 and M247.003 as closed Prop-valued definitions; prefix the namespace
with Langlands.NYLL; rename the targets; use focused Mathlib-only imports.
The original theorem proofs and CompleteDVF construction are not included.
-/

import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Native adic topology and adic completeness: statement targets

These closed propositions preserve the supplied `Valued` structure and the
independent field and value-group universes of NYLL M247.002 and M247.003.
They state the original conclusions without proving them.
-/

universe u v

namespace Langlands.NYLL.ValuationTheory.Valuations

/-- The native subtype topology on a rank-one discrete valuation subring is
its maximal-ideal adic topology. This is a proposition target, not a proof. -/
def RankOneDiscreteValuationSubringIsAdicStatement : Prop :=
  ∀ {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma]
    [Valued K Gamma]
    [(Valued.v : _root_.Valuation K Gamma).IsRankOneDiscrete],
    IsAdic
      (IsLocalRing.maximalIdeal
        (Valued.v : _root_.Valuation K Gamma).valuationSubring)

/-- Completeness for the supplied valued uniformity implies maximal-ideal
adic completeness of the valuation subring. This is a proposition target. -/
def RankOneDiscreteValuationSubringIsAdicCompleteStatement : Prop :=
  ∀ {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma]
    [Valued K Gamma]
    [(Valued.v : _root_.Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K],
    IsAdicComplete
      (IsLocalRing.maximalIdeal
        (Valued.v : _root_.Valuation K Gamma).valuationSubring)
      (Valued.v : _root_.Valuation K Gamma).valuationSubring

end Langlands.NYLL.ValuationTheory.Valuations
