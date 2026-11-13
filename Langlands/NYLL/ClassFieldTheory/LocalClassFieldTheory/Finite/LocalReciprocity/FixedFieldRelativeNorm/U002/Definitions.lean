/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M276.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix and keep the source section
variables, docstring and body, including the well-definedness proof.
Replace the source imports by Mathlib.FieldTheory.IsSepClosed and the
published modules defining the abstract fixed fields, the relative fixed
field and the extension subgroup, and open only the namespace of
extensionSubgroup. Omit the local Fintype instance
M276.001 and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions

/-!
# Cosets of a relative fixing subgroup as field embeddings

A left coset of the abstract fixing subgroup of an upper fixed field, inside
the fixing subgroup of a lower fixed field, restricts to an embedding of the
upper fixed field into the common ambient field over the lower one.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]

/-- A left coset of the abstract fixing subgroup restricts to an embedding
of the upper concrete fixed field into the common ambient field. -/
def abstractFixedFieldCosetToAlgHom
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) →
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
      (abstractRelativeFixedField k Ω hLK).val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈ extensionSubgroup K L hLK :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : L.toSubgroup := ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion hLK η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix : η.1 (x : Ω) = (x : Ω) :=
        (IntermediateField.mem_fixedField_iff L.toSubgroup
          (x : Ω)).1 x.property η.1 η.2
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηfix.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by
          have hτ' := congrArg Subtype.val hτ
          change τ.1 = σ.1 * η.1 at hτ'
          rw [hτ'])

end Langlands.NYLL.LocalClassFieldTheory

end
