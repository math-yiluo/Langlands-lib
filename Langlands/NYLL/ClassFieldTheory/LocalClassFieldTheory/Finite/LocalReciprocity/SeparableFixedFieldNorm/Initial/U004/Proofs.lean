/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Statements

/-!
# Cosets of the base fixing subgroup as embeddings: injectivity

Adapted by Worker 368, 14 November 2026, from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M165.004 (the private
source theorem `LocalClassFieldTheory.baseFixingCosetToAlgHom_injective`),
published under the reserved name `Langlands.NYLL.PortInternal.M165.d004`
with the published `d004Statement` as its type. The source section
variables are written as explicit binders. The unpublished source lemma
`mem_extensionSubgroup_iff` is replaced by Mathlib's
`Subgroup.mem_subgroupOf`; the rest of the proof is the source proof.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

/-- Two left cosets of `Gal(Ω / E)` in `Gal(Ω / K)` with the same restriction
to `E` are equal: the coset restriction map is injective. -/
theorem _root_.Langlands.NYLL.PortInternal.M165.d004
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω) :
    Langlands.NYLL.PortInternal.M165.d004Statement K Ω E := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply (Subgroup.mem_subgroupOf).2
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  have hy := congrArg (fun ψ : E →ₐ[K] Ω => ψ y) hqr
  change (Quotient.out q).1 (y : Ω) =
    (Quotient.out r).1 (y : Ω) at hy
  change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
  rw [← hy]
  simp [y]

end
end Langlands.NYLL.LocalClassFieldTheory
