/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 331, 2026-11-14: extract M353.002 as the public port-internal abbreviation d002,
reuse the published LocalField and LinearTerm definitions, and focus imports
and documentation. Preserve the subtype body and effective source binders.
See the paired Markdown. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions

/-! # Bundled power series with a prescribed linear term -/

noncomputable section

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

/-- The subtype of multivariable series with prescribed linear term `L`. -/
abbrev d002 (L : sigma → F.valuationSubring) :=
  {H : MvPowerSeries sigma F.valuationSubring // HasLinearTerm H L}

end Langlands.NYLL.PortInternal.M353

end
