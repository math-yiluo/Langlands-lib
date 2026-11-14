/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Statements

/-!
# Cosets of the base fixing subgroup as embeddings: surjectivity

Adapted by Worker 368, 14 November 2026, from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M165.003 (the private
source theorem `LocalClassFieldTheory.baseFixingCosetToAlgHom_surjective`),
published under the reserved name `Langlands.NYLL.PortInternal.M165.d003`
with the published `d003Statement` as its type. The source section
variables are written as explicit binders; the proof is the source proof.
The paired Markdown records the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

/-- Every `K`-embedding of a finite separable intermediate field `E` into a
separably closed Galois extension `Ω / K` is the restriction of an
automorphism of `Ω / K`: the coset restriction map is surjective. -/
theorem _root_.Langlands.NYLL.PortInternal.M165.d003
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Langlands.NYLL.PortInternal.M165.d003Statement K Ω E := by
  intro f
  let : Algebra.IsSeparable E Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := K) (L := E) (M := Ω) (E := Ω)) f
  let σ : Ω ≃ₐ[K] Ω :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id K Ω)).1
  have hσ : σ ∈ (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  let σbase : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup := ⟨σ, hσ⟩
  refine ⟨QuotientGroup.mk σbase, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun ψ : E →ₐ[K] Ω => ψ x) hφ
  change φ (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

end
end Langlands.NYLL.LocalClassFieldTheory
