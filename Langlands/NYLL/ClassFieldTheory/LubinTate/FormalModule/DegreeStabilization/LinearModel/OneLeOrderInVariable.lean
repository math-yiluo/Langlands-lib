/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 792, 2026-11-16: extract source-private theorem M351.014
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as the public
theorem Langlands.NYLL.PortInternal.M351.d014, typed by its published
proposition target. Replace source imports and opened namespaces by focused
Library imports and Langlands.NYLL namespaces. Retain the source proof and
elaborated binders; omit the unused source section settings. Add focused
documentation. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.ConstantCoeffInVariable

/-!
# Order of the Lubin–Tate series inserted into a variable

Proof of the published M351.014 target: `ebar(X_i)` has order at least one.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- The inserted Lubin–Tate series `ebar(X_i)` has order at least one
(NYLL M351.014). -/
theorem d014 (ebar : LubinTateSeries F π) (i : σ) :
    d014Statement ebar i :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)

end Langlands.NYLL.PortInternal.M351
