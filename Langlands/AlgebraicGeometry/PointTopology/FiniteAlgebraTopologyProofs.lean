import Langlands.AlgebraicGeometry.PointTopology.FiniteAlgebraTopologyStatements
import Mathlib.LinearAlgebra.Unimodular
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Splitting and topology of a finite projective ring extension -/

noncomputable section

open Topology
open scoped BigOperators

namespace Langlands.AlgebraicGeometry.PointTopology

theorem finiteProjectiveAlgebra_isUnimodular_one
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S] [FaithfulSMul R S] :
    Module.IsUnimodular R (1 : S) := by
  classical
  let I : Ideal R := LinearMap.range (LinearMap.applyₗ (R := R) (1 : S))
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R S
  have hexpand : ∑ i, (s 1) i • p (Pi.single i 1) = (1 : S) := by
    simpa only [← map_smul, ← map_sum, ← pi_eq_sum_univ',
      LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hps 1
  have hmap : I.map (algebraMap R S) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hexpand]
    apply (I.map (algebraMap R S)).sum_mem
    intro i _
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_right _ _
    apply Ideal.mem_map_of_mem _
    exact ⟨(LinearMap.proj i).comp s, rfl⟩
  have hI : I = ⊤ :=
    (Ideal.map_eq_top_iff (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S)
      (algebraMap_isIntegral_iff.mpr inferInstance)).mp hmap
  exact (show (1 : R) ∈ I from hI ▸ Submodule.mem_top)

theorem finiteProjectiveAlgebraTopologyProperties_proof
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S] [FaithfulSMul R S] :
    FiniteProjectiveAlgebraTopologyProperties R S := by
  let _ : TopologicalSpace S := moduleTopology R S
  let _ : IsTopologicalRing S := IsModuleTopology.isTopologicalRing R S
  obtain ⟨l, hl⟩ := finiteProjectiveAlgebra_isUnimodular_one R S
  have hleft : Function.LeftInverse l (algebraMap R S) := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one]
  refine ⟨inferInstance, l, hleft, IsModuleTopology.continuous_of_linearMap l, ?_⟩
  exact hleft.isEmbedding
    (IsModuleTopology.continuous_of_linearMap l)
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R S))

end Langlands.AlgebraicGeometry.PointTopology
