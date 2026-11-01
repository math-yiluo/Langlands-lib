/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 1 November 2026:
Extract only the proof of M093.027 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed NormQuotientSelfEqOneStatement
by introducing its three internal binders, then retain the original
quotient-induction proof through the public NormQuotient.inductionOn,
normClass_eq_one_iff_mem and localNormSubgroup_self.
Import only U027.Statements and preserve its entire public chain.
Retain the sole universe u and canonical self-algebra; omit the original
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U027.Statements

/-!
# Norm classes for the identity extension

Proof of the closed assertion that every norm class for the identity
extension is the identity of the actual norm quotient.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Every norm class for the identity extension is the identity. -/
theorem normQuotient_self_eq_one : NormQuotientSelfEqOneStatement.{u} := by
  intro K _ x
  refine NormQuotient.inductionOn (motive := fun q => q = 1) x ?_
  intro a
  exact (normClass_eq_one_iff_mem K K a).2 (by
    rw [localNormSubgroup_self K]
    exact Subgroup.mem_top a)

end Langlands.NYLL.LocalFieldTheory
