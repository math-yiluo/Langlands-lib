/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 31 October 2026:
Extract the statement of M093.015 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all eleven source term binders inside a closed
Prop-valued definition, preserving their order, binder kinds and independent
universes u/v. Import only the published U014 Definitions module and omit
the source proof, simp attribute, noncomputable section and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U014.Definitions

/-!
# First-isomorphism equivalence on norm classes

The closed proposition specifying evaluation of the published norm-quotient
first-isomorphism equivalence at the class of a base-field unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The first-isomorphism equivalence sends a norm class to the image of its representative. -/
def NormQuotientEquivOfSurjectiveNormClassStatement : Prop :=
  ∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) (x : Kˣ),
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x

end Langlands.NYLL.LocalFieldTheory
