/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1153, 31 October 2026:
Extract the proof of M093.015 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its eleven internal binders, then following the original proof unchanged.
Import only U015 Statements. Restore the original simp behavior through
an explicit-telescope wrapper derived from the exact closed theorem:
registering the closed theorem itself does not simplify representatives.
Omit the source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U015.Statements

/-!
# First-isomorphism equivalence on norm classes

The canonical first-isomorphism equivalence evaluates at a norm class
as the supplied homomorphism evaluates at the same representative.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The first-isomorphism equivalence sends a norm class to the image of its representative. -/
theorem normQuotientEquivOfSurjective_normClass :
    NormQuotientEquivOfSurjectiveNormClassStatement.{u,v} := by
  intro K L M _ _ _ _ f hf hker x
  change
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))
        (QuotientGroup.mk x) = f x
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Explicit-telescope simp form of the closed representative equation. -/
@[simp]
theorem normQuotientEquivOfSurjective_normClass_apply
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) (x : Kˣ) :
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x :=
  normQuotientEquivOfSurjective_normClass f hf hker x

end Langlands.NYLL.LocalFieldTheory
