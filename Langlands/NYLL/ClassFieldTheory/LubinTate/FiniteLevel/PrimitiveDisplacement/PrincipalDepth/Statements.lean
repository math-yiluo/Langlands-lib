/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299 and Worker 469, 2026-11-13/14: extract the
principal-depth helpers M362.022 and M362.026 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, expose the private names as PortInternal.M362.d022Statement
and d026Statement, and replace theorem bodies by Prop-valued definitions.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions

/-! # Exact principal-unit depth: statements (NYLL M362.022, M362.026) -/

noncomputable section

universe u v

namespace Langlands.NYLL.PortInternal.M362

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- NYLL M362.022: an exact principal-unit layer gives a unit times the
corresponding uniformizer power. -/
def d022Statement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) (k : ℕ)
    (_ha : a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k)
    (_hnot : a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1)) : Prop :=
  ∃ c : F.valuationSubringˣ,
    (a : F.valuationSubring) - 1 = (c : F.valuationSubring) * π ^ k

/-- NYLL M362.026: a unit times a uniformizer power determines all
principal-unit levels. -/
def d026Statement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a c : F.valuationSubringˣ) (r k : ℕ)
    (_hsub : (a : F.valuationSubring) - 1 =
      (c : F.valuationSubring) * π ^ r) : Prop :=
  a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k ↔ k ≤ r

end Langlands.NYLL.PortInternal.M362
