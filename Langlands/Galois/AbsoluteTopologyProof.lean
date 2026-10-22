import Langlands.Galois.AbsoluteTopologyStatement
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-! # Compactness of the full-closure absolute Galois group -/

namespace Langlands.GaloisRepresentation

open IntermediateField
open scoped Topology

universe u v w

private theorem continuous_restrictScalars (K : Type u) (P : Type v) (L : Type w)
    [Field K] [Field P] [Field L] [Algebra K P] [Algebra P L] [Algebra K L]
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
  exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ x (subset_adjoin P _ hx)

private theorem restrictScalars_surjective_of_purelyInseparable
    (K : Type u) (P : Type v) (L : Type w)
    [Field K] [Field P] [Field L] [Algebra K P] [Algebra P L] [Algebra K L]
    [IsScalarTower K P L] [IsPurelyInseparable K P] :
    Function.Surjective (AlgEquiv.restrictScalarsHom K : Gal(L/P) →* Gal(L/K)) := by
  intro σ
  have hfix : ∀ x : P, σ (algebraMap P L x) = algebraMap P L x := by
    intro x
    exact DFunLike.congr_fun
      (Subsingleton.elim (σ.toAlgHom.comp (IsScalarTower.toAlgHom K P L))
        (IsScalarTower.toAlgHom K P L)) x
  refine ⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩
  rfl

/-- Compactness in the existing Krull topology, including imperfect base fields. -/
theorem absoluteGaloisGroupCompactness : AbsoluteGaloisGroupCompactness.{u} := by
  intro K _
  let P := perfectClosure K (AlgebraicClosure K)
  have : IsGalois P (AlgebraicClosure K) := ⟨⟩
  exact Function.Surjective.compactSpace
    (continuous_restrictScalars K P (AlgebraicClosure K))
    (restrictScalars_surjective_of_purelyInseparable K P (AlgebraicClosure K))

end Langlands.GaloisRepresentation
