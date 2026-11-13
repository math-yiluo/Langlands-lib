/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source definition
LocalClassFieldTheory.baseFixingCosetToAlgHom (inventory M165.001) as
Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom. The section
variables, the type and the body (including its well-definedness proof) are
unchanged. The namespace is prefixed with Langlands.NYLL; the NYLL imports are
replaced by the published modules defining closedFixingSubgroup,
extensionSubgroup and fixingSubgroupLeBase, next to the source's Mathlib
import; only the two opened namespaces these names need are kept. All other
source declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs

/-!
# Cosets of the base fixing subgroup as embeddings: the restriction map

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`,
lines 36–37 (section variables), 41 and 43–79 (inventory M165.001).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section CosetsAndEmbeddings

variable (E : IntermediateField K Ω)

/-- Restriction to `E` sends a left coset of `Gal(Ω/E)` to the corresponding
`K`-embedding of `E` into `Ω`. -/
def baseFixingCosetToAlgHom :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) →
      (E →ₐ[K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => σ.1.toAlgHom.comp E.val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈
          extensionSubgroup
            (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : (closedFixingSubgroup K Ω E).toSubgroup :=
        ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion
          (fixingSubgroupLeBase K Ω E) η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix :=
        (IntermediateField.mem_fixingSubgroup_iff E η.1).mp η.2
      have hηx : η.1 (x : Ω) = (x : Ω) := hηfix x x.2
      have hτ' := congrArg Subtype.val hτ
      change τ.1 = σ.1 * η.1 at hτ'
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηx.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by rw [hτ'])

end CosetsAndEmbeddings

end
end Langlands.NYLL.LocalClassFieldTheory
