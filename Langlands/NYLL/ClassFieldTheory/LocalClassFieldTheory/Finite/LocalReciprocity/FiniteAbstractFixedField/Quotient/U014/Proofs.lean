/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 4913, 14 November 2026 UTC:
Extract only the proof of M099.014 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published FiniteAbstractFixedField
Quotient Statements module and open only RamificationTheory. State the
theorem as the published Statement applied to the source parameters, in
which extensionSubgroup K L hLK is written as its body
L.toSubgroup.subgroupOf K.toSubgroup, and write the change target with the
same body. The proof is otherwise unchanged. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Quotient.Statements

/-!
# Kernel of the relative quotient homomorphism

The proof that the kernel of `abstractRelativeToAmbientQuotient` is exactly the
relative subgroup `L.toSubgroup.subgroupOf K.toSubgroup`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The kernel of the preceding quotient map is the exact abstract class-formation
relative subgroup. -/
theorem abstractRelativeToAmbientQuotient_ker
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    abstractRelativeToAmbientQuotient_kerStatement k Ω K L hLK hnormal := by
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  ext σ
  change
    QuotientGroup.mk' (abstractRelativeFixedField k Ω hLK).fixingSubgroup
        (abstractSubgroupEquivGaloisGroup k Ω K σ) = 1 ↔
      σ ∈ L.toSubgroup.subgroupOf K.toSubgroup
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK]
  constructor
  · rintro ⟨τ, hτ, hτσ⟩
    have : τ = σ :=
      (abstractSubgroupEquivGaloisGroup k Ω K).injective hτσ
    simpa [this] using hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

end Langlands.NYLL.LocalClassFieldTheory
