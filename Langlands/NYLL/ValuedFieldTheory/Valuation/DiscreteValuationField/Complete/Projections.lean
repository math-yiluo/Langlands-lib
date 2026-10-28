/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 764, 2026-10-27: extract only M107.007–012 (lines 116–147)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace with Langlands.NYLL, import the two published definition
modules, flatten the parent-structure fields of toHenselianDVF and write
the stored value-group structure and rank-one discreteness explicitly,
replace the tactic proof calling the intervening theorem
Valuation.henselianRing by Mathlib's IsAdicComplete.henselianRing with a
local instance from the stored adic-completeness proof, and reword the
docstrings of the four residue-data abbreviations.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Definitions

/-!
# Forgetful projections and residue data of complete discrete valuation fields

This module adapts the six abbreviations in lines 116–147 of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`.
A complete DVF is viewed as a Henselian DVF with the same chosen valuation;
all weaker data are read along the path `CompleteDVF → HenselianDVF → DVF`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

noncomputable section

universe u v

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- A complete DVF is Henselian.  This is the canonical forgetful projection:
all weaker DVF data are obtained through this object. -/
abbrev toHenselianDVF (F : CompleteDVF.{u, v} K) : HenselianDVF.{u, v} K where
  ValueGroup := F.ValueGroup
  instValueGroup := F.instValueGroup
  valuation := F.valuation
  instRankOneDiscrete := F.instCompleteDiscrete.isRankOneDiscrete
  instHenselian :=
    letI : IsAdicComplete (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
        F.valuation.valuationSubring :=
      F.instCompleteDiscrete.isAdicComplete
    IsAdicComplete.henselianRing F.valuation.valuationSubring
      (IsLocalRing.maximalIdeal F.valuation.valuationSubring)

/-- The underlying DVF, obtained along the canonical
`CompleteDVF -> HenselianDVF -> DVF` path. -/
abbrev toDVF (F : CompleteDVF.{u, v} K) : DVF.{u, v} K :=
  F.toHenselianDVF.toDVF

/-- The valuation subring of the underlying Henselian DVF, viewed as a type. -/
abbrev valuationSubring (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.valuationSubring

/-- The canonical maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : CompleteDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toHenselianDVF.maximalIdeal

/-- The residue field of the valuation subring. -/
abbrev residueField (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.residueField

/-- The canonical residue map of the valuation subring. -/
abbrev residueMap (F : CompleteDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toHenselianDVF.residueMap

end CompleteDVF

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
