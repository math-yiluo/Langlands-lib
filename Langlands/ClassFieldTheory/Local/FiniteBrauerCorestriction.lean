import Langlands.ClassFieldTheory.Local.BrauerLocalCorestriction
import Langlands.ClassFieldTheory.Local.MatrixTransferFactorSet
import Langlands.ClassFieldTheory.Local.TwoCocycleTransfer

noncomputable section

open Langlands.Brauer Langlands.BrauerComparison Langlands.BrauerCorestriction
open Langlands.CentralSimple Langlands.CentralSimple.SemilinearGaloisAction
open Langlands.Continuous
open Matrix
open scoped TensorProduct

namespace Langlands.ClassFieldTheory.Local

universe u v w

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
  [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] (hcont : Continuous (algebraMap K L))

include hcont

local notation "S" => SeparableClosure K
local notation "T" => SeparableClosure L

section Chart

variable (N : OpenNormalSubgroup Gal(SeparableClosure K/K))
  (hN : N.toSubgroup ≤ (separableClosureBase K L).fixingSubgroup) (A : CSA.{u, u} L)

include N hN

set_option quotPrecheck false in
local notation "M" => ↥(separableClosureStageField K N)

variable {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]

set_option maxHeartbeats 1000000 in
private theorem inflated_relativeCorestriction_at_chart :
    letI := separableClosureStageAlgebra K L N hN
    letI := separableClosureStageTowerBase K L N hN
    letI := fixedField_openNormal_finiteDimensional K S N
    ∀ e : M ⊗[L] A ≃ₐ[M] Matrix I I M,
      relativeToContinuous K M S 2 (relativeCorestriction K L M 2 (relativeClass e)) =
        brauerEquiv K (classOf (corCSA K L A)) := by
  let := separableClosureStageAlgebra K L N hN
  let := separableClosureStageTowerBase K L N hN
  let := fixedField_openNormal_finiteDimensional K S N
  let := separableClosureStageTopAlgebra K L N
  let := separableClosureStageTowerTop K L N hN
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  intro e
  have hA : brauerEquiv L (classOf A) = relativeToContinuous L M T 2 (relativeClass e) :=
    brauerContinuousEquiv_at_chart L T A M e
  rw [← separableUnitCorestriction_relativeToContinuous K L N hN 2, ← hA]
  exact (brauerEquiv_corestriction K L hcont (classOf A)).symm

set_option maxHeartbeats 1000000 in
/-- Relative corestriction takes the class of an upper splitting chart to
the class of any chart of its actual tensor corestriction over the same field. -/
theorem relativeClass_corestriction {J : Type w} [Fintype J] [DecidableEq J] [Nonempty J] :
    letI := separableClosureStageAlgebra K L N hN
    letI := separableClosureStageTowerBase K L N hN
    letI := fixedField_openNormal_finiteDimensional K S N
    ∀ (e : M ⊗[L] A ≃ₐ[M] Matrix I I M)
      (f : M ⊗[K] (corCSA K L A) ≃ₐ[M] Matrix J J M),
      relativeCorestriction K L M 2 (relativeClass e) = relativeClass f := by
  let := separableClosureStageAlgebra K L N hN
  let := separableClosureStageTowerBase K L N hN
  let := fixedField_openNormal_finiteDimensional K S N
  intro e f
  apply relativeToContinuous_fixedStage_injective K S N
  exact (inflated_relativeCorestriction_at_chart K L hcont N hN A e).trans
    (brauerContinuousEquiv_at_chart K S (corCSA K L A) M f)

set_option maxHeartbeats 1000000 in
/-- The class of the corestriction chart is represented by the transfer
of the original chart's positive scalar factor cocycle. -/
theorem relativeClass_corestriction_H2π {J : Type w} [Fintype J] [DecidableEq J] [Nonempty J] :
    letI := separableClosureStageAlgebra K L N hN
    letI := separableClosureStageTowerBase K L N hN
    letI := fixedField_openNormal_finiteDimensional K S N
    ∀ (e : M ⊗[L] A ≃ₐ[M] Matrix I I M)
      (f : M ⊗[K] (corCSA K L A) ≃ₐ[M] Matrix J J M),
      let ρ := splittingChartIndexAction e
      relativeClass f = groupCohomology.H2π (unitsRepresentation K M)
        (relativeTransferCocycle₂ K L M (unitCocycle ρ.scalarDefect ρ.scalarDefect_isTwoCocycle)) := by
  let := separableClosureStageAlgebra K L N hN
  let := separableClosureStageTowerBase K L N hN
  let := fixedField_openNormal_finiteDimensional K S N
  intro e f
  rw [← relativeClass_corestriction K L hcont N hN A e f]
  exact relativeCorestriction_H2π K L M _

omit hcont [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
set_option maxHeartbeats 1000000 in
/-- The Kronecker construction from the upper chart has the transferred scalar factors. -/
theorem tensorTransferMatrixLift_mul_at_chart (m : ℕ) [Nonempty (Fin m)] :
    letI := separableClosureStageAlgebra K L N hN
    letI := separableClosureStageTowerBase K L N hN
    letI := fixedField_openNormal_finiteDimensional K S N
    let H := relativeGaloisSubgroup K L M
    letI : Fintype (Gal(M/K) ⧸ H) := Fintype.ofFinite _
    letI : DecidableEq (Gal(M/K) ⧸ H) := Classical.decEq _
    ∀ e : M ⊗[L] A ≃ₐ[M] Matrix (Fin m) (Fin m) M,
      let ρ := splittingChartIndexAction e
      let r := relativeGaloisSubgroupEquiv K L M
      let P := tensorTransferMatrixLift K M H m (fun h => ρ.innerMatrix (r.symm h))
      let c := relativeTransferCocycle₂ K L M (unitCocycle ρ.scalarDefect ρ.scalarDefect_isTwoCocycle)
      ∀ s t : Gal(M/K),
        P s * GeneralLinearGroup.map s.toRingHom (P t) =
          GeneralLinearGroup.scalar ((Gal(M/K) ⧸ H) → Fin m) (Additive.toMul (c (s, t))) *
            P (s * t) := by
  let := separableClosureStageAlgebra K L N hN
  let := separableClosureStageTowerBase K L N hN
  let := fixedField_openNormal_finiteDimensional K S N
  let H := relativeGaloisSubgroup K L M
  let : Fintype (Gal(M/K) ⧸ H) := Fintype.ofFinite _
  let : DecidableEq (Gal(M/K) ⧸ H) := Classical.decEq _
  dsimp only
  intro e s t
  let ρ := splittingChartIndexAction e
  let r := relativeGaloisSubgroupEquiv K L M
  have hr (a : H) : (r.symm a).restrictScalars K = (a : Gal(M/K)) :=
    congrArg Subtype.val (r.apply_symm_apply a)
  have hlift (a b : H) :
      ρ.innerMatrix (r.symm a) *
        GeneralLinearGroup.map (a : Gal(M/K)).toRingHom (ρ.innerMatrix (r.symm b)) =
        GeneralLinearGroup.scalar (Fin m) (ρ.scalarDefect (r.symm a) (r.symm b)) *
          ρ.innerMatrix (r.symm (a * b)) := by
    rw [← hr a, map_mul]
    exact ρ.innerMatrix_mul (r.symm a) (r.symm b)
  rw [relativeTransferCocycle₂_apply]
  exact tensorTransferMatrixLift_mul K M H m _ _ hlift s t

set_option maxHeartbeats 1000000 in
/-- The same finite stage splits the actual corestriction if it splits the upper algebra. -/
theorem isSplit_corestriction_baseChange_of_chart :
    letI := separableClosureStageAlgebra K L N hN
    (M ⊗[L] A ≃ₐ[M] Matrix I I M) → IsSplit (baseChange M (corCSA K L A)) := by
  let := separableClosureStageAlgebra K L N hN
  let := separableClosureStageTowerBase K L N hN
  let := fixedField_openNormal_finiteDimensional K S N
  let : DecidableEq Gal(M/K) := Classical.decEq _
  intro e
  obtain ⟨B, f, hf⟩ := exists_relativeClass_eq (relativeCorestriction K L M 2 (relativeClass e))
  have hB := brauerContinuousEquiv_at_chart K S B M f
  rw [hf] at hB
  have hC : classOf (corCSA K L A) = classOf B := (brauerEquiv K).injective
    ((inflated_relativeCorestriction_at_chart K L hcont N hN A e).symm.trans hB.symm)
  apply (classOf_eq_zero_iff _).mp
  rw [← scalarExtension_classOf, hC, scalarExtension_classOf]
  exact (classOf_eq_zero_iff _).mpr ⟨Fintype.card Gal(M/K), Fintype.card_pos,
    ⟨f.trans (Matrix.reindexAlgEquiv M M (Fintype.equivFin Gal(M/K)))⟩⟩

/-- A positive-size splitting chart of the actual corestriction over the upper splitting stage. -/
def corestrictionSplittingChart :
    letI := separableClosureStageAlgebra K L N hN
    (M ⊗[L] A ≃ₐ[M] Matrix I I M) →
      Σ n : ℕ, {_f : M ⊗[K] (corCSA K L A) ≃ₐ[M] Matrix (Fin n) (Fin n) M // 0 < n} := by
  let := separableClosureStageAlgebra K L N hN
  intro e
  have hsplit := isSplit_corestriction_baseChange_of_chart K L hcont N hN A e
  exact ⟨hsplit.choose, ⟨hsplit.choose_spec.2.some, hsplit.choose_spec.1⟩⟩

end Chart

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Every upper algebra and its actual corestriction admit charts over a common finite Galois
stage containing the upper base field. -/
theorem exists_corestrictionSplittingCharts (A : CSA.{u, u} L) :
    ∃ (N : OpenNormalSubgroup Gal(S/K))
      (hN : N.toSubgroup ≤ (separableClosureBase K L).fixingSubgroup),
      let M := separableClosureStageField K N
      letI := separableClosureStageAlgebra K L N hN
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        Nonempty (M ⊗[L] A ≃ₐ[M] Matrix (Fin m) (Fin m) M) ∧
        Nonempty (M ⊗[K] (corCSA K L A) ≃ₐ[M] Matrix (Fin n) (Fin n) M) := by
  let F := separableSplittingStage L T A
  let i : F →ₐ[L] T := IsScalarTower.toAlgHom L F T
  obtain ⟨N, hN, j, _⟩ := exists_separableClosureStage_containing K L F i
  let M := separableClosureStageField K N
  let : Algebra L M := separableClosureStageAlgebra K L N hN
  let : Algebra F M := j.toRingHom.toAlgebra
  let : IsScalarTower L F M := IsScalarTower.of_algHom j
  let m := CentralSimple.reducedDegree L A
  have hm : 0 < m := CentralSimple.reducedDegree_pos L A
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let e : M ⊗[L] A ≃ₐ[M] Matrix (Fin m) (Fin m) M :=
    enlargedSplittingChart M (separableSplittingChart L T A)
  let f := corestrictionSplittingChart K L hcont N hN A e
  exact ⟨N, hN, m, f.1, hm, f.2.2, ⟨e⟩, ⟨f.2.1⟩⟩

end Langlands.ClassFieldTheory.Local
