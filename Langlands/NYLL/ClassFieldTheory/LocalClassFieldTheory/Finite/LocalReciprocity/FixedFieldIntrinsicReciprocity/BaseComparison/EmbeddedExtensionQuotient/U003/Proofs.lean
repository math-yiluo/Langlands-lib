/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normalStatement
of M274.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U003 Statements module. Replace the
source proof (transport of normality from the intrinsic abstract base along
intrinsicBaseEquivAmbientEmbeddedField) by a direct Mathlib proof: an element
fixing the image of F is an F-algebra map for the algebra structure given by
i, so by AlgHom.fieldRange_of_normal it maps the normal image of E into
itself. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U003.Statements

/-!
# Normality of embedded extension subgroups

The proof of the published closed proposition that the fixing subgroup of the
image of a finite Galois extension `E / F` is normal in the fixing subgroup of
the image of `F`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The fixing subgroup cut out by an embedded finite Galois extension is
normal inside the fixing subgroup of its embedded base field. -/
theorem ambientEmbeddedExtensionSubgroup_normal :
    ambientEmbeddedExtensionSubgroup_normalStatement := by
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j i e _e H₀ J₀
  have hmaps : ∀ h ∈ (AlgHom.fieldRange i).fixingSubgroup,
      ∀ x ∈ AlgHom.fieldRange j, h x ∈ AlgHom.fieldRange j := by
    intro h hh x hx
    let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
    let jF : E →ₐ[F] SeparableClosure K :=
      { j.toRingHom with commutes' := fun _ => rfl }
    let EF : IntermediateField F (SeparableClosure K) := jF.fieldRange
    have : Normal F EF := Normal.of_algEquiv (AlgEquiv.ofInjectiveField jF)
    let hF : SeparableClosure K →ₐ[F] SeparableClosure K :=
      { (h : SeparableClosure K ≃ₐ[K] SeparableClosure K).toRingHom with
        commutes' := fun y =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _ ⟨y, rfl⟩ }
    have hrange := AlgHom.fieldRange_of_normal (hF.comp EF.val)
    obtain ⟨y, rfl⟩ := hx
    have hmem : h (j y) ∈ (hF.comp EF.val).fieldRange := ⟨⟨j y, y, rfl⟩, rfl⟩
    rw [hrange] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, hz⟩
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : Gal(SeparableClosure K / K)) ∈ (AlgHom.fieldRange j).fixingSubgroup := hn
  have hg : (g : Gal(SeparableClosure K / K))⁻¹ ∈
      (AlgHom.fieldRange i).fixingSubgroup := (g⁻¹).2
  change ((g * n * g⁻¹ : H₀.toSubgroup) : Gal(SeparableClosure K / K)) ∈
    (AlgHom.fieldRange j).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hn' ⊢
  intro x hx
  have hy := hmaps _ hg x hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
  rw [hn' _ hy, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end Langlands.NYLL.LocalClassFieldTheory
