/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 125, 2026-11-13: extract only M334.009 (lines 78–80)
and M334.012 (lines 95–98) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace and
opened namespace with Langlands.NYLL, replace the source imports by the
published LocalField.Basic.Definitions module and Mathlib.Algebra.CharP.Defs,
remove the unused universes w and x, and replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Mathlib.Algebra.CharP.Defs

/-!
# Residue characteristic of a chosen local-field package

This module extracts the residue-characteristic abbreviation and its
`CharP` instance from
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
-/

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

open Langlands.NYLL.ValuationTheory.DiscreteValuationField

namespace LocalField

variable {K : Type u} [Field K]

/-- The residue characteristic of a local field. -/
noncomputable abbrev residueCharacteristic (F : LocalField.{u, v} K) : ℕ :=
  ringChar F.residueField

/-- The target has the stated characteristic: `CharP F.residueField F.residueCharacteristic`. -/
instance residueField_charP_residueCharacteristic (F : LocalField.{u, v} K) :
    CharP F.residueField F.residueCharacteristic :=
  ringChar.charP (R := F.residueField)

end LocalField

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
