/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 294, 2026-11-14: focused extraction of M353.032,
namespace qualification, source-private name adaptation, Statement target,
and replacement of the recursive imports by focused published dependencies.
Prepared for submission by Worker 295, 2026-11-16: verified the pinned source,
retained Worker 294's proof preparation, and expanded source/credit documentation.
The accompanying Markdown records exact source correspondence and edits.
License and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.StepStatements

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

theorem d032
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    d032Statement hm target H d := by
  change MvPowerSeries.coeff d.1 (d030 hm target H d).1 =
      MvPowerSeries.coeff d.1 target
  simp [d030, MvPowerSeries.coeff_monomial_same]

end Langlands.NYLL.PortInternal.M353
