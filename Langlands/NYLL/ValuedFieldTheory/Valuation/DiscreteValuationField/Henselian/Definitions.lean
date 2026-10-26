/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 54, 2026-10-26: extract only M104.007–011 (lines 190–216)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace with Langlands.NYLL and import the published DVF module.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Henselian

/-!
# Henselian discrete valuation fields and residue data

The bundle extends the chosen discrete valuation field with supplied
Henselianity at the actual maximal ideal of its valuation ring.
The four abbreviations reuse the canonical data of the underlying DVF.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

noncomputable section

universe u v

/-- A Henselian discretely valued field. -/
structure HenselianDVF (K : Type u) [Field K] extends DVF.{u, v} K where
  /-- The valuation ring is Henselian along its maximal ideal. -/
  [instHenselian : HenselianRing toDVF.valuationSubring toDVF.maximalIdeal]

attribute [instance] HenselianDVF.instHenselian

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- The valuation subring of the underlying DVF, viewed as a type. -/
abbrev valuationSubring (F : HenselianDVF.{u, v} K) : Type u :=
  F.toDVF.valuationSubring

/-- The canonical maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : HenselianDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toDVF.maximalIdeal

/-- The residue field of the valuation subring. -/
abbrev residueField (F : HenselianDVF.{u, v} K) : Type u :=
  F.toDVF.residueField

/-- The canonical residue map of the valuation subring. -/
abbrev residueMap (F : HenselianDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toDVF.residueMap

end HenselianDVF

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
