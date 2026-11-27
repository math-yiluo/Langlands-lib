import Langlands.Galois.Local.SeparableUnramifiedNormedCompletion
import Mathlib.FieldTheory.KrullTopology

/-! # Continuous Galois evaluation on the normed unramified completion -/

noncomputable section

universe u

namespace Langlands.LocalGalois.Separable.UnramifiedCompletion

open scoped Topology
open Filter

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem completedFieldAut_coe_eventually_eq (σ : Gal(inertiaFixedField F/F))
    (a : NormedFixedField F) :
    ∀ᶠ τ : Gal(inertiaFixedField F/F) in 𝓝 σ,
      completedFieldAut F τ (a : CompletedField F) = completedFieldAut F σ (a : CompletedField F) := by
  let x := fixedFieldEquiv F a
  let H := MulAction.stabilizer Gal(inertiaFixedField F/F) x
  have hH : IsOpen (H : Set Gal(inertiaFixedField F/F)) :=
    stabilizer_isOpen_of_isIntegral (K := F) x
  have hpre : IsOpen ((fun τ : Gal(inertiaFixedField F/F) => σ⁻¹ * τ) ⁻¹' (H : Set _)) :=
    hH.preimage (continuous_const.mul continuous_id)
  have hσ : σ ∈ (fun τ : Gal(inertiaFixedField F/F) => σ⁻¹ * τ) ⁻¹' (H : Set _) := by
    change σ⁻¹ * σ ∈ H
    rw [inv_mul_cancel]
    exact H.one_mem
  filter_upwards [hpre.mem_nhds hσ] with τ hτ
  have ht : (σ⁻¹ * τ) x = x := hτ
  have h : τ x = σ x := by
    apply σ.symm.injective
    simpa only [AlgEquiv.mul_apply, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply] using ht
  rw [completedFieldAut_coe, completedFieldAut_coe]
  exact congrArg (fun z : inertiaFixedField F =>
    ((fixedFieldEquiv F).symm z : CompletedField F)) h

/-- The orbit of each completed field element is continuous for the Krull topology. -/
theorem completedFieldAut_orbitContinuous (x : CompletedField F) :
    Continuous (fun σ : Gal(inertiaFixedField F/F) => completedFieldAut F σ x) := by
  rw [continuous_iff_continuousAt]
  intro σ
  apply Metric.continuousAt_iff'.2
  intro ε hε
  obtain ⟨a, ha⟩ := Metric.mem_closure_range_iff.mp
    (UniformSpace.Completion.denseRange_coe x) (ε / 2) (by positivity)
  filter_upwards [completedFieldAut_coe_eventually_eq F σ a] with τ hτ
  calc
    dist (completedFieldAut F τ x) (completedFieldAut F σ x) ≤
        dist (completedFieldAut F τ x) (completedFieldAut F τ (a : CompletedField F)) +
          dist (completedFieldAut F τ (a : CompletedField F)) (completedFieldAut F σ x) :=
      dist_triangle _ _ _
    _ = dist x (a : CompletedField F) + dist (a : CompletedField F) x := by
      rw [(completedFieldAut_isometry F τ).dist_eq, hτ, (completedFieldAut_isometry F σ).dist_eq]
    _ < ε := by rw [dist_comm (a : CompletedField F) x]; linarith

/-- Evaluation of the canonical isometric Galois action is jointly continuous. -/
theorem completedFieldAut_continuous :
    Continuous (fun z : Gal(inertiaFixedField F/F) × CompletedField F => completedFieldAut F z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply Metric.continuousAt_iff'.2
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hd : ∀ᶠ p in 𝓝 z, dist (Prod.snd p) z.2 < ε / 2 :=
    Metric.continuousAt_iff'.1 continuous_snd.continuousAt (ε / 2) hhalf
  have hc : Continuous (fun p : Gal(inertiaFixedField F/F) × CompletedField F =>
      completedFieldAut F p.1 z.2) := (completedFieldAut_orbitContinuous F z.2).comp continuous_fst
  have horbit := Metric.continuousAt_iff'.1 (hc.continuousAt (x := z)) (ε / 2) hhalf
  filter_upwards [hd, horbit] with p hp hσ
  calc
    dist (completedFieldAut F p.1 p.2) (completedFieldAut F z.1 z.2) ≤
        dist (completedFieldAut F p.1 p.2) (completedFieldAut F p.1 z.2) +
          dist (completedFieldAut F p.1 z.2) (completedFieldAut F z.1 z.2) :=
      dist_triangle _ _ _
    _ = dist p.2 z.2 + dist (completedFieldAut F p.1 z.2) (completedFieldAut F z.1 z.2) := by
      rw [(completedFieldAut_isometry F p.1).dist_eq]
    _ < ε := by linarith

/-- The action on the actual normed completion obtained by extending each Galois automorphism. -/
@[instance_reducible]
def completedFieldMulAction : MulAction Gal(inertiaFixedField F/F) (CompletedField F) where
  smul σ x := completedFieldGaloisAction F σ x
  one_smul x := by
    change (completedFieldGaloisAction F 1) x = x
    rw [map_one]
    rfl
  mul_smul σ τ x := by
    change (completedFieldGaloisAction F (σ * τ)) x =
      (completedFieldGaloisAction F σ) ((completedFieldGaloisAction F τ) x)
    rw [map_mul]
    rfl

/-- The induced action is continuous for the Krull topology on the unramified Galois group. -/
theorem completedFieldMulAction_continuousSMul :
    letI := completedFieldMulAction F
    ContinuousSMul Gal(inertiaFixedField F/F) (CompletedField F) :=
  ⟨completedFieldAut_continuous F⟩

end Langlands.LocalGalois.Separable.UnramifiedCompletion
