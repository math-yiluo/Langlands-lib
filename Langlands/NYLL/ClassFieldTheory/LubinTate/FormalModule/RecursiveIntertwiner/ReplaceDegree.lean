/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 325, 14 November 2026: extract the source private
replaceDegree data M353.040, give it the planned PortInternal.M353.d040
name, and replace dependencies by the published focused definition modules.
The body and effective source telescope are unchanged. See the paired
Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Definitions

noncomputable section

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

/-- Replace every coefficient of one total degree by the corresponding
coefficient of a target series. -/
noncomputable def d040
    {L : sigma → F.valuationSubring}
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (m : ℕ) (hm : 2 ≤ m) :
    d002 (F := F) L :=
  d031 hm target (d003 (sigma := sigma) m) H

end Langlands.NYLL.PortInternal.M353

end
