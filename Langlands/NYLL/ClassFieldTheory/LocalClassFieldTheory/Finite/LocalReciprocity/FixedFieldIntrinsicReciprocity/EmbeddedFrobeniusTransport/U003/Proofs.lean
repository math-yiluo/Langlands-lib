/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuousStatement
of M281.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import the published U002 Statements module and the published
proof of continuous_algEquiv_autCongr. Replace the source proof (continuity
of the conjugation theta via unpublished semilinear-conjugation lemmas,
composed with the M281.002 theorem for e0) by a direct argument: the map is
tau ↦ (autCongr e tau).restrictScalars K for the scalar tower K → F → the
ambient closure given by i, which is continuous by a private lemma
continuous_restrictScalarsHom, copied from the private Library lemma
continuous_restrictScalars in Langlands/Galois/AbsoluteTopologyProof.lean,
and the published continuous_algEquiv_autCongr. Omit all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U002.Statements
import Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U001.Proofs

/-!
# Continuity of the embedded intrinsic-to-ambient base equivalence

The proof of the published closed proposition that
`intrinsicBaseEquivAmbientEmbeddedField K F i e` is continuous.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open IntermediateField
open RamificationTheory CyclicCohomology ClassFormation

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

/-- The intrinsic absolute Galois equivalence induced by an embedding into the
ambient separable closure is continuous. -/
theorem intrinsicBaseEquivAmbientEmbeddedField_continuous :
    intrinsicBaseEquivAmbientEmbeddedField_continuousStatement := by
  intro K F _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e
  have : IsScalarTower K F (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  have : Algebra.IsAlgebraic F (SeparableClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) F
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  refine Continuous.congr
    ((continuous_restrictScalarsHom K F (SeparableClosure K)).comp
      ((AlgebraicNumberTheory.continuous_algEquiv_autCongr e).comp
        continuous_subtype_val)) ?_
  intro tau
  apply AlgEquiv.ext
  intro x
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    ((AlgEquiv.ofInjectiveField i).trans
      (IntermediateField.equivOfEq
        (InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)).symm)).toLinearEquiv.finiteDimensional
  let : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  let : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  show e (tau.1 (e.symm x)) =
    e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x))))))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end Langlands.NYLL.LocalClassFieldTheory
