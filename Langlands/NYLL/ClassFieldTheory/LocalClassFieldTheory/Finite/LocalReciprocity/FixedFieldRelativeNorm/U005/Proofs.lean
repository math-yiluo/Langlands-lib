/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of the private theorem M276.005
abstractFixedFieldCosetToAlgHom_injective from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709,
as the theorem Langlands.NYLL.PortInternal.M276.d005 proving the published
d005Statement. Introduce the statement's binders and keep the source tactic
proof, with the published names opened, except that the unpublished source
lemma KummerTheory.mem_extensionSubgroup_iff is replaced by Mathlib's
Subgroup.mem_subgroupOf, which states the same membership criterion for
the subgroupOf body of extensionSubgroup.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Statements

/-!
# Distinct relative cosets give distinct embeddings: proof
-/

namespace Langlands.NYLL.PortInternal.M276

open Langlands.NYLL.LocalClassFieldTheory

/-- Distinct relative left cosets give distinct embeddings of the upper
fixed field (source unit M276.005). -/
theorem d005 : d005Statement := by
  intro k Ω _ _ _ _ K L hLK q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply Subgroup.mem_subgroupOf.2
  have hfix : (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈
      (abstractFixedField k Ω L).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : abstractRelativeFixedField k Ω hLK := ⟨x, hx⟩
    have hy := congrArg
      (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω => ψ y) hqr
    change (Quotient.out q).1 (y : Ω) =
      (Quotient.out r).1 (y : Ω) at hy
    change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
    rw [← hy]
    simp [y]
  rw [InfiniteGalois.fixingSubgroup_fixedField L] at hfix
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ L.toSubgroup
  exact hfix

end Langlands.NYLL.PortInternal.M276
