import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Representation.FiniteVectors
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact

/-! # Compactly parametrized bounded orbit averages -/

noncomputable section

open MeasureTheory Set Topology
open scoped ContDiff Manifold Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section Parameter

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
  {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : G →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  (j : C(X, G)) (w : C(X, ℂ))

omit [CompleteSpace E] in
include hR in
theorem integrable_compactWeightedOrbit (v : E) : Integrable (fun x => w x • R (j x) v) ν :=
  (w.continuous.smul (hR.comp (j.continuous.prodMk continuous_const))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The compactly parametrized weighted Bochner orbit integral as a bounded operator. -/
def compactWeightedOrbit : E →L[ℂ] E := by
  let T : E →ₗ[ℂ] E :=
    { toFun := fun v => ∫ x, w x • R (j x) v ∂ν
      map_add' := fun u v => by
        simp only [map_add, smul_add, integral_add (integrable_compactWeightedOrbit ν R hR j w u)
          (integrable_compactWeightedOrbit ν R hR j w v)]
      map_smul' := fun c v => by
        simp only [map_smul, smul_comm _ c, integral_smul, RingHom.id_apply] }
  apply T.mkContinuousOfExistsBound
  have hc (v : E) : Continuous (fun x => R (j x) v) :=
    hR.comp (j.continuous.prodMk continuous_const)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun x => R (j x)) fun v => by
    obtain ⟨b, hb⟩ := isCompact_univ.exists_bound_of_continuousOn (hc v).continuousOn
    exact ⟨b, fun x => hb x (mem_univ x)⟩
  refine ⟨‖w‖ * max C 0 * ν.real univ, fun v => ?_⟩
  change ‖∫ x, w x • R (j x) v ∂ν‖ ≤ _
  calc
    _ ≤ (‖w‖ * max C 0 * ‖v‖) * ν.real univ := by
      apply norm_integral_le_of_norm_le_const
      apply Filter.Eventually.of_forall
      intro x
      rw [norm_smul, mul_assoc]
      exact mul_le_mul (w.norm_coe_le_norm x)
        (((R (j x)).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right ((hC x).trans (le_max_left C 0)) (norm_nonneg v)))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-- Pointwise formula for the compactly parametrized average. -/
@[simp]
theorem compactWeightedOrbit_apply (v : E) :
    compactWeightedOrbit ν R hR j w v = ∫ x, w x • R (j x) v ∂ν :=
  rfl

end Parameter

section CompactSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : G →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ)
  (F : (Fin d → ℂ) →ₗ[ℂ] C(K, ℂ))
  (hF : ∀ (k x : K) (u : Fin d → ℂ), F (τ k *ᵥ u) x = F u (k⁻¹ * x))

local notation "j" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(K, G))

include hF in
/-- Averaging a finite translation type against an orbit gives an intertwiner from
that type into the original compact action. -/
def compactWeightedIntertwiner (v : E) : intertwiners R K d τ := by
  have hint (u : Fin d → ℂ) : Integrable (fun k : K => F u k • R (k : G) v) ν :=
    integrable_compactWeightedOrbit ν R hR j (F u) v
  let T : (Fin d → ℂ) →ₗ[ℂ] E :=
    { toFun := fun u => ∫ k, F u k • R (k : G) v ∂ν
      map_add' := fun u z => by
        simp only [map_add, ContinuousMap.add_apply, add_smul, integral_add (hint u) (hint z)]
      map_smul' := fun c u => by
        simp only [map_smul, ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul,
          mul_smul, integral_smul] }
  refine ⟨T, fun k u => ?_⟩
  change (∫ x, F (τ k *ᵥ u) x • R (x : G) v ∂ν) =
    R (k : G) (∫ x, F u x • R (x : G) v ∂ν)
  rw [← integral_mul_left_eq_self _ k, ← (R (k : G)).integral_comp_comm (hint u)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    change F (τ k *ᵥ u) (k * x) • R ((k * x : K) : G) v =
      R (k : G) (F u x • R (x : G) v)
    rw [hF, inv_mul_cancel_left, Subgroup.coe_mul, map_mul, mul_apply_eq_comp, map_smul])

include hF in
/-- Admissibility bounds the range of the averaged action with any weight in the
specified finite translation type. -/
theorem finiteDimensional_range_compactWeightedOrbit (hadm : IsAdmissible R K)
    (hτ : Continuous τ) (u : Fin d → ℂ) :
    FiniteDimensional ℂ (compactWeightedOrbit ν R hR j (F u)).toLinearMap.range := by
  let T : intertwiners R K d τ →ₗ[ℂ] E :=
    { toFun := fun t => t.val u
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let : FiniteDimensional ℂ (intertwiners R K d τ) := hadm d τ hτ
  apply Submodule.finiteDimensional_of_le (S₂ := T.range)
  rintro _ ⟨v, rfl⟩
  exact ⟨compactWeightedIntertwiner K ν R hR τ F hF v, rfl⟩

/-- The original normed representation restricted to the subgroup and regarded algebraically. -/
def normCompactRepresentation : Representation ℂ K E :=
  ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (R.comp K.subtype)

include hF in
/-- Each averaged vector is compact-finite, since it is the image of a vector of the
given finite translation type under a compact intertwiner. -/
theorem isFiniteVector_compactWeightedOrbit (u : Fin d → ℂ) (v : E) :
    FiniteVectors.IsFiniteVector (normCompactRepresentation K R)
      (compactWeightedOrbit ν R hR j (F u) v) := by
  let T := compactWeightedIntertwiner K ν R hR τ F hF v
  let S : Subrepresentation (normCompactRepresentation K R) :=
    { toSubmodule := T.val.range
      apply_mem_toSubmodule := by
        intro k x
        rintro ⟨z, rfl⟩
        exact ⟨τ k *ᵥ z, T.property k z⟩ }
  let : FiniteDimensional ℂ S.toSubmodule := LinearMap.finiteDimensional_range T.val
  exact FiniteVectors.isFiniteVector_of_mem _ S ⟨u, rfl⟩

end CompactSubgroup

end Langlands.Archimedean
