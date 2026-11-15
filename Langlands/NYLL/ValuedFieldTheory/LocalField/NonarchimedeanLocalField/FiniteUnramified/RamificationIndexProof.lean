/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 4699, 2026-11-15: prove the published closed target of M161.002,
the theorem IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one at
lines 46–55 of Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, under the same name
prefixed with Langlands.NYLL. The theorem's type is the published closed proposition,
so the source binders become an opening intro, and the source term proof (lines 54–55,
the field projection of the published M161.001 class) becomes an exact step. The
source imports are replaced by the published statement module. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.RamificationIndexStatement

/-!
# Ramification index of an unramified valued extension: proof

This module proves the published closed target for NYLL M161.002.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel

/-- An unramified valued extension has ramification index one. This proves the
closed target for NYLL M161.002. -/
theorem unramifiedValuation_ramificationIdx_eq_one :
    unramifiedValuation_ramificationIdx_eq_oneStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _
  exact IsUnramifiedValuedExtension.maximalIdeal_ramificationIdx_eq_one
    (K := K) (L := L)

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
