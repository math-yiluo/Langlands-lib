/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Group.Units.Hom

/-!
# Finite extensions of discretely valued fields: degree, ramification index, residue degree

Modified by Worker 5264, 15 November 2026: port the source definitions M108.001
`ValuedExtension.degree`, M108.003 `ValuedExtension.ramificationIndex`, M108.004
`ValuedExtension.residueDegree` and M108.054 `ValuedExtension.IsDefectless` of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 with their source variables and bodies.
Prefix the namespace with `Langlands.NYLL`, import the published
`DiscreteValuationField.Basic` module instead of the source `ResidueField` and
`Complete` modules, and omit the other source declarations. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The field degree of a finite valued extension. -/
def degree (_base : DVF.{u, v} K) (_target : DVF.{w, x} L) : ℕ :=
  Module.finrank K L

/-- The canonical ramification index of the target maximal ideal over the
base maximal ideal. -/
noncomputable def ramificationIndex : ℕ :=
  Ideal.ramificationIdx'
    (base.maximalIdeal : Ideal base.valuationSubring)
    (target.maximalIdeal : Ideal target.valuationSubring)

/-- The canonical residue degree of the target maximal ideal over the base
maximal ideal. -/
noncomputable def residueDegree : ℕ :=
  (target.maximalIdeal : Ideal target.valuationSubring).inertiaDeg
    base.valuationSubring

/-- Defectlessness is the exact fundamental equality. -/
def IsDefectless : Prop :=
  degree base target =
    ramificationIndex base target * residueDegree base target

end ValuedExtension
end DiscreteValuationField
end
end Langlands.NYLL.ValuationTheory
