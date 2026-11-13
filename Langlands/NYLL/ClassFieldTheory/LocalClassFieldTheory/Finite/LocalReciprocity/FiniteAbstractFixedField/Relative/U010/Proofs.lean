/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M099.010 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published FiniteAbstractFixedField
Relative Statements module and open only RamificationTheory. State the
theorem as the published Statement applied to the source parameters, in which
extensionSubgroup K L hLK is written as its body
L.toSubgroup.subgroupOf K.toSubgroup. The two uses of the unpublished
KummerTheory.mem_extensionSubgroup_iff (source proof Iff.rfl) are replaced by
Mathlib's Subgroup.mem_subgroupOf, with the intermediate membership stated
in L.toSubgroup. The published abstractSubgroupEquivGaloisGroup_apply
(source proof rfl) in the first calc step is replaced by rfl. The rest of the
proof is unchanged. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Statements

/-!
# Image of the relative subgroup under the abstract Galois equivalence

The proof that `abstractSubgroupEquivGaloisGroup k Ω K` maps the subgroup
`L.toSubgroup.subgroupOf K.toSubgroup` onto the fixing subgroup of the upper
fixed field, regarded over the lower fixed field.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Under the preceding Galois-group equivalence, the relative class-formation
subgroup is exactly the subgroup fixing the upper concrete field. -/
theorem map_extensionSubgroup_abstractSubgroupEquiv
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    map_extensionSubgroup_abstractSubgroupEquivStatement k Ω K L hLK := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσL : (σ.1 : Gal(Ω/k)) ∈ L.toSubgroup :=
      Subgroup.mem_subgroupOf.1 hσ
    have hfix : ∀ y ∈ abstractFixedField k Ω L, σ.1 y = y := by
      have hσfix : σ.1 ∈ (abstractFixedField k Ω L).fixingSubgroup := by
        rw [InfiniteGalois.fixingSubgroup_fixedField L]
        exact hσL
      exact (IntermediateField.mem_fixingSubgroup_iff
        (abstractFixedField k Ω L) σ.1).1 hσfix
    exact hfix x hx
  · intro hτ
    let σ : K.toSubgroup :=
      (abstractSubgroupEquivGaloisGroup k Ω K).symm τ
    refine ⟨σ, ?_, (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ⟩
    apply Subgroup.mem_subgroupOf.2
    have hσfix : (σ.1 : Gal(Ω/k)) ∈
        (abstractFixedField k Ω L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hτfix := (IntermediateField.mem_fixingSubgroup_iff
        (abstractRelativeFixedField k Ω hLK) τ).1 hτ x hx
      calc
        σ.1 x = abstractSubgroupEquivGaloisGroup k Ω K σ x := rfl
        _ = τ x := by
          rw [show abstractSubgroupEquivGaloisGroup k Ω K σ = τ by
            exact (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ]
        _ = x := hτfix
    rw [InfiniteGalois.fixingSubgroup_fixedField L] at hσfix
    exact hσfix

end Langlands.NYLL.LocalClassFieldTheory
