/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026, and Worker 437, 15 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement
of M274.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709, following the source proof.
Add the Langlands.NYLL namespace prefix. Import the published U001
Statements module, which contains the statement, and the published proof
module of M273.008, intrinsicBaseEquivAmbientEmbeddedField_apply_val,
instead of the source imports. Name the M273.008 instance used hval. Omit
the source's local data EI, H₀, J₀ and hJH, which the proof does not use
after the statement's own local data is unfolded.
Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U001.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U008.Proofs

/-!
# Embedded extension quotients: membership in the transported extension subgroup

The proof of the published closed proposition that, under
`intrinsicBaseEquivAmbientEmbeddedField`, membership in the intrinsic
extension subgroup of an embedded finite Galois extension `E / F` is
equivalent to membership of the image in the ambient extension subgroup.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- Under the embedded-field base equivalence, membership in the intrinsic
extension subgroup for `E / F` is equivalent to membership in the ambient
extension subgroup determined by the two field ranges. -/
theorem intrinsicExtensionSubgroup_iff_ambientEmbeddedField :
    intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement := by
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  -- The pointwise formula of M273.008 for this `tau`.
  have hval :
      ∀ x : SeparableClosure K,
        (intrinsicBaseEquivAmbientEmbeddedField K F i e tau).1.1 x =
          e (tau.1 (e.symm x)) :=
    intrinsicBaseEquivAmbientEmbeddedField_apply_val K F i e tau
  change
    tau.1 ∈ (AlgHom.fieldRange jI).fixingSubgroup ↔
      (intrinsicBaseEquivAmbientEmbeddedField
        K F i e tau).1 ∈
          (AlgHom.fieldRange j).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro htau x hx
    obtain ⟨y, rfl⟩ := hx
    change
      (intrinsicBaseEquivAmbientEmbeddedField
        K F i e tau).1.1 (j y) = j y
    rw [hval]
    change e (tau.1 (jI y)) = j y
    rw [htau (jI y) ⟨y, rfl⟩]
    exact e.apply_symm_apply (j y)
  · intro hpsi x hx
    obtain ⟨y, rfl⟩ := hx
    apply e.injective
    change
      e (tau.1 (e.symm (j y))) =
        e (e.symm (j y))
    rw [e.apply_symm_apply]
    rw [← hval]
    exact hpsi (j y) ⟨y, rfl⟩

end Langlands.NYLL.LocalClassFieldTheory
