/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M140.006 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean,
lines 90-99, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace with Langlands.NYLL, import only the published Valuation Statements
module, and prove the published target applied to all its parameters with the
original proof. Omit the theorem-only simp attribute, the source noncomputable
section and all other source declarations. See the paired Markdown; the
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements

/-!
# The Galois action on the value group is trivial

Every Galois automorphism fixes every element of the multiplicative value
group `Multiplicative ℤ` under the source trivial action.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u

/-- The source Galois action on the value group is trivial. -/
theorem galoisGroupValueGroupMulDistribMulAction_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (n : Multiplicative Int) :
    galoisGroupValueGroupMulDistribMulAction_smulStatement K L σ n := by
  unfold galoisGroupValueGroupMulDistribMulAction_smulStatement
  intro hValueAction
  rfl

end Langlands.NYLL.LocalClassFieldTheory
