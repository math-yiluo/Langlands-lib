/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 4913, 14 November 2026 UTC:
Extract only the proof of M099.015 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published FiniteAbstractFixedField
Quotient Statements module and open only RamificationTheory. State the
theorem as the published Statement applied to the source parameters, in which
extensionSubgroup K L hLK is written as its body
L.toSubgroup.subgroupOf K.toSubgroup. The proof is otherwise unchanged. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Quotient.Statements

/-!
# Surjectivity of the relative quotient homomorphism

The proof that `abstractRelativeToAmbientQuotient` is surjective.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The quotient map from the abstract lower subgroup is surjective. -/
theorem abstractRelativeToAmbientQuotient_surjective
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    abstractRelativeToAmbientQuotient_surjectiveStatement k Ω K L hLK hnormal := by
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  intro q
  refine Quotient.inductionOn' q ?_
  intro τ
  refine ⟨(abstractSubgroupEquivGaloisGroup k Ω K).symm τ, ?_⟩
  change QuotientGroup.mk
    (abstractSubgroupEquivGaloisGroup k Ω K
      ((abstractSubgroupEquivGaloisGroup k Ω K).symm τ)) =
      QuotientGroup.mk τ
  rw [(abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply]

end Langlands.NYLL.LocalClassFieldTheory
