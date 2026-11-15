/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

/-!
# Targets: adic completeness and basic ideal data of complete discrete valuation fields

Modified by Worker 5264, 15 November 2026: state the source theorems M107.002
`Valuation.isAdicComplete`, M107.013
`CompleteDVF.valuationSubring_isDiscreteValuationRing`, M107.014
`CompleteDVF.isAdicComplete`, M107.017 `CompleteDVF.mem_valuationSubring_iff`,
M107.022 `CompleteDVF.exists_uniformizer`, M107.023
`CompleteDVF.uniformizer_mem_maximalIdeal` and M107.032
`CompleteDVF.maximalIdeal_ne_bot` of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, omit the proofs, the universe `w` and the rest of the source
file, import the published `Complete.Projections` module instead of the
source imports, and turn off the unused-variable linter for the hypothesis
`hpi` of M107.023, which the proposition does not mention. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

namespace Valuation

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- Target: completeness of the valued field implies adic completeness of its
valuation subring. -/
def isAdicCompleteStatement (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] : Prop :=
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring

end Valuation

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- Target: the valuation subring in the complete model is a discrete valuation
ring. -/
def valuationSubring_isDiscreteValuationRingStatement (F : CompleteDVF.{u, v} K) : Prop :=
    IsDiscreteValuationRing F.valuationSubring

/-- Target: the complete DVR model is complete for its maximal-ideal-adic
topology. -/
def isAdicCompleteStatement (F : CompleteDVF.{u, v} K) : Prop :=
    IsAdicComplete F.maximalIdeal F.valuationSubring

/-- Target: membership in the valuation subring is characterized by
nonnegative valuation. -/
def mem_valuationSubring_iffStatement (F : CompleteDVF.{u, v} K) (x : K) : Prop :=
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1

/-- Target: a complete discrete valuation field admits a uniformizer. -/
def exists_uniformizerStatement (F : CompleteDVF.{u, v} K) : Prop :=
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K))

set_option linter.unusedVariables false in
/-- Target: every chosen uniformizer lies in the maximal ideal. -/
def uniformizer_mem_maximalIdealStatement (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) : Prop :=
    pi ∈ F.maximalIdeal

/-- Target: the maximal ideal of a complete DVF valuation ring is nonzero. -/
def maximalIdeal_ne_botStatement (F : CompleteDVF.{u, v} K) : Prop :=
    F.maximalIdeal ≠ ⊥

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
