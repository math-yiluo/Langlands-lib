/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_continuousStatement
of M281.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import the published U002 Statements module and the published
proof of continuous_algEquiv_autCongr. Replace the unpublished source lemma
Field.absoluteGaloisGroup.ofIntermediateFieldInExtension_continuous by a
private lemma continuous_restrictScalarsHom whose proof is copied from the
private Library lemma continuous_restrictScalars in
Langlands/Galois/AbsoluteTopologyProof.lean, and the source lemma
Field.absoluteGaloisGroup.algEquiv_autCongr_continuous by the published
continuous_algEquiv_autCongr. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
Worker 698, 14 November 2026: adopted the shared draft proof unchanged;
checked source correspondence and updated its paired documentation.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U002.Statements
import Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U001.Proofs

/-!
# Continuity of the fixed-field intrinsic-to-ambient base equivalence

The proof of the published closed proposition that
`intrinsicBaseEquivAmbientFixedField K H e` is continuous.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open IntermediateField

/-- Restricting scalars from an intermediate field to the base is continuous
for the Krull topologies (local copy of a private Library lemma). -/
private theorem continuous_restrictScalarsHom
    (K P L : Type) [Field K] [Field P] [Field L]
    [Algebra K P] [Algebra P L] [Algebra K L]
    [IsScalarTower K P L] [Algebra.IsAlgebraic P L] :
    Continuous (AlgEquiv.restrictScalarsHom K : Gal(L/P) →* Gal(L/K)) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hEN⟩ := hN
  let := hE
  obtain ⟨s, hs⟩ := (essFiniteType_iff (K := E)).mp inferInstance
  let F : IntermediateField P L := adjoin P (s : Set L)
  have : FiniteDimensional P F :=
    finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  apply (krullTopology_mem_nhds_one_iff P L _).mpr
  refine ⟨F, inferInstance, ?_⟩
  intro σ hσ
  apply hEN
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hs]
  apply (forall_mem_adjoin_smul_eq_self_iff K (σ.restrictScalars K)).mpr
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ x
    (subset_adjoin P _ hx)

/-- The equivalence on absolute Galois base subgroups induced by a fixed-field
separable-closure equivalence is continuous. -/
theorem intrinsicBaseEquivAmbientFixedField_continuous :
    intrinsicBaseEquivAmbientFixedField_continuousStatement := by
  intro K _ H F e
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  refine Continuous.congr
    ((continuous_restrictScalarsHom K F (SeparableClosure K)).comp
      ((AlgebraicNumberTheory.continuous_algEquiv_autCongr e).comp
        continuous_subtype_val)) ?_
  intro tau
  rfl

end Langlands.NYLL.LocalClassFieldTheory
