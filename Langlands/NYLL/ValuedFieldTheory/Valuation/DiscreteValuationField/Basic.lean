/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 384, 2026-10-25: extract the chosen valuation and basic
residue data from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
qualify the namespace with Langlands.NYLL and reuse canonical Mathlib
instances instead of the four redundant source instance aliases.
The retained license and notices are in licenses/NYLL/.
-/

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Chosen discrete valuation fields and basic residue data

This module adapts only the data declarations in lines 37–87 of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`.
The valuation subring and residue field use their canonical Mathlib instances.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

noncomputable section

universe u v

/-- A field with a chosen rank-one discrete valuation. -/
structure DVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group. -/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group. -/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field. -/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation has discrete rank one. -/
  [instRankOneDiscrete : valuation.IsRankOneDiscrete]

attribute [instance] DVF.instValueGroup DVF.instRankOneDiscrete

namespace DVF

variable {K : Type u} [Field K]

/-- The valuation subring of a DVF, viewed as a type. -/
abbrev valuationSubring (F : DVF.{u, v} K) : Type u :=
  F.valuation.valuationSubring

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : DVF.{u, v} K) : Ideal F.valuationSubring :=
  IsLocalRing.maximalIdeal F.valuationSubring

/-- The residue field of the valuation subring. -/
abbrev residueField (F : DVF.{u, v} K) : Type u :=
  IsLocalRing.ResidueField F.valuationSubring

/-- The canonical residue map of a DVF. -/
abbrev residueMap (F : DVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  IsLocalRing.residue F.valuationSubring

end DVF

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
