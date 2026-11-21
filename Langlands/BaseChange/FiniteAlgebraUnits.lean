import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix

noncomputable section

open Filter Matrix Set Topology

namespace Langlands.BaseChange

variable {F A : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T1Space F]
variable [Ring A] [Algebra F A] [Module.Finite F A]
variable [TopologicalSpace A] [IsModuleTopology F A]

include F

/-- In a finite algebra with the module topology, the unit group is an open subspace. -/
theorem finiteAlgebra_isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Aˣ → A) := by
  classical
  let : ContinuousAdd A := IsModuleTopology.toContinuousAdd F A
  let b := Module.finBasis F A
  let ρ := Algebra.leftMulMatrix b
  have hρ : Continuous ρ := IsModuleTopology.continuous_of_linearMap ρ.toLinearMap
  have hdet (a : A) : (ρ a).det ≠ 0 ↔ IsUnit a := by
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, Algebra.leftMulMatrix_apply,
      LinearMap.isUnit_toMatrix_iff, Algebra.lmul_isUnit_iff]
  let f (a : A) : A := b.equivFun.symm ((ρ a)⁻¹ *ᵥ b.equivFun 1)
  have hf : ContinuousOn f {a : A | IsUnit a} := by
    have hb : Continuous b.equivFun.symm :=
      IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
    have hi : ContinuousOn (fun a : A => (ρ a)⁻¹) {a : A | IsUnit a} := by
      intro a ha
      apply ContinuousAt.continuousWithinAt
      apply (continuousAt_matrix_inv _ ?_).comp hρ.continuousAt
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ ((hdet a).2 ha)
    have hv : Continuous (fun M : Matrix (Fin (Module.finrank F A))
        (Fin (Module.finrank F A)) F => M *ᵥ b.equivFun 1) :=
      continuous_id.matrix_mulVec continuous_const
    exact (hb.comp hv).comp_continuousOn hi
  have hfu (a : Aˣ) : f a.val = (↑a⁻¹ : A) := by
    have hinv : (ρ a.val)⁻¹ = ρ (↑a⁻¹ : A) := by
      let u := Units.map ρ.toMonoidHom a
      change (u.val)⁻¹ = (Units.map ρ.toMonoidHom a⁻¹).val
      rw [map_inv]
      exact (Matrix.coe_units_inv u).symm
    apply b.equivFun.injective
    change b.equivFun (b.equivFun.symm ((ρ a.val)⁻¹ *ᵥ b.equivFun 1)) =
      b.equivFun (↑a⁻¹ : A)
    rw [LinearEquiv.apply_symm_apply, hinv]
    have h := Algebra.leftMulMatrix_mulVec_repr b (↑a⁻¹ : A) 1
    simpa [Module.Basis.equivFun_apply, ρ] using h
  refine ⟨Units.isEmbedding_val_mk' hf hfu, ?_⟩
  have hrange : range (Units.val : Aˣ → A) = (fun a => (ρ a).det) ⁻¹' {0}ᶜ := by
    ext a
    exact (show IsUnit a ↔ (ρ a).det ≠ 0 from (hdet a).symm)
  rw [hrange]
  exact isOpen_compl_singleton.preimage hρ.matrix_det

/-- A family tending to a unit eventually lifts to a family converging in the unit group. -/
theorem finiteAlgebra_exists_tendsto_unit {Z : Type*} {L : Filter Z}
    {f : Z → A} {a : Aˣ} (hf : Tendsto f L (𝓝 (a : A))) :
    ∃ g : Z → Aˣ, Tendsto g L (𝓝 a) ∧ ∀ᶠ z in L, (g z : A) = f z := by
  classical
  let g (z : Z) : Aˣ := if hz : IsUnit (f z) then hz.unit else 1
  have he := finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := A)
  have hunit : ∀ᶠ z in L, f z ∈ range (Units.val : Aˣ → A) :=
    hf.eventually (he.isOpen_range.mem_nhds (mem_range_self a))
  have hg : (Units.val ∘ g) =ᶠ[L] f := hunit.mono fun z hz => by
    have hz' : IsUnit (f z) := hz
    simp only [Function.comp_apply, g, dite_eq_left hz', hz'.unit_spec]
  exact ⟨g, he.tendsto_nhds_iff.mpr (hf.congr' hg.symm), hg⟩

end Langlands.BaseChange
