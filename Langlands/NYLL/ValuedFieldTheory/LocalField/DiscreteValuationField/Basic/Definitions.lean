/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 320, 2026-11-13: extract only M334.001–005 (lines 34–59)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace and opened namespace with Langlands.NYLL, replace the
source imports by the published Complete.Projections module, remove
the unused universes w and x, and replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

/-!
# Chosen local-field package and residue data

This module extracts the local-field structure and four residue-data
abbreviations from `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
-/

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

open Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- A local field with a chosen complete discrete valuation and finite residue field. -/
structure LocalField (K : Type u) [Field K] extends CompleteDVF.{u, v} K where
  /-- The residue field of the chosen complete discrete valuation is finite. -/
  [residueFinite : Finite toCompleteDVF.residueField]

attribute [instance] LocalField.residueFinite

namespace LocalField

variable {K : Type u} [Field K]

/-- The residue field of a local field package. -/
abbrev residueField (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.residueField

/-- The valuation subring of a local field package. -/
abbrev valuationSubring (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.valuationSubring

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : LocalField.{u, v} K) : Ideal F.valuationSubring :=
  F.toCompleteDVF.maximalIdeal

/-- The residue map of a local field package. -/
abbrev residueMap (F : LocalField.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toCompleteDVF.residueMap

end LocalField

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
