/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 13 November 2026: extract the specified M140
declarations from commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace by Langlands.NYLL and reduce imports to the
published data used in the declarations. Theorems are represented by
Prop-valued definitions with the Statement suffix and unchanged statements.
Data construction bodies and their local instance scope are preserved.
See the paired Markdown; LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Action.Units
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The source action on field units, using Mathlib's canonical action. -/
@[implicit_reducible]
def galoisGroupFieldUnitsMulDistribMulAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MulDistribMulAction (Gal(L / K)) Lˣ :=
  inferInstance

/-- The source trivial Galois action on the multiplicative integer value group. -/
@[implicit_reducible]
def galoisGroupValueGroupMulDistribMulAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MulDistribMulAction (Gal(L / K)) (Multiplicative Int) where
  smul _ n := n
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
  smul_mul := by intro _ m n; rfl
  smul_one := by intro _; rfl

end
end Langlands.NYLL.LocalClassFieldTheory
