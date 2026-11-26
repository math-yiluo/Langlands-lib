import Langlands.Galois.Local.SeparableUnramifiedFrobenius
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.MetricSpace.Completion

/-! # The normed completion of the actual maximal unramified extension -/

noncomputable section

universe u

namespace Langlands.LocalGalois.Separable.UnramifiedCompletion

open scoped NNReal
open UniformSpace.Completion

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

/-- The real absolute value of the inherited valuation on the inertia fixed field. -/
def fixedFieldAbsoluteValue : AbsoluteValue (inertiaFixedField F) ℝ where
  toFun x := (fixedFieldValuation F x : ℝ)
  map_mul' x y := by simp only [map_mul, NNReal.coe_mul]
  nonneg' _ := NNReal.coe_nonneg _
  eq_zero' _ := by simp only [NNReal.coe_eq_zero, map_eq_zero]
  add_le' x y := by
    rcases le_max_iff.mp ((fixedFieldValuation F).map_add x y) with h | h
    · exact (NNReal.coe_le_coe.mpr h).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))
    · exact (NNReal.coe_le_coe.mpr h).trans (le_add_of_nonneg_left (NNReal.coe_nonneg _))

/-- The inertia fixed field with its inherited absolute value. -/
abbrev NormedFixedField := WithAbs (fixedFieldAbsoluteValue F)

/-- The valued model is algebraically the actual inertia fixed field. -/
def fixedFieldEquiv : NormedFixedField F ≃ₐ[F] inertiaFixedField F :=
  WithAbs.algEquiv F (fixedFieldAbsoluteValue F)

/-- The norm agrees with the spectral norm that defines the inertia fixed-field valuation. -/
theorem norm_fixedField_eq (x : NormedFixedField F) :
    ‖x‖ = spectralNorm F (inertiaFixedField F) (fixedFieldEquiv F x) := by
  change (fixedFieldValuation F (fixedFieldEquiv F x) : ℝ) = _
  rw [fixedFieldValuation_eq_spectralValuation]
  rfl

instance instNormedFixedFieldUltrametric : IsUltrametricDist (NormedFixedField F) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  change (fixedFieldValuation F (fixedFieldEquiv F (x + y)) : ℝ) ≤
    max (fixedFieldValuation F (fixedFieldEquiv F x) : ℝ) (fixedFieldValuation F (fixedFieldEquiv F y) : ℝ)
  have hxy : (fixedFieldEquiv F) (x + y) = (fixedFieldEquiv F) x + (fixedFieldEquiv F) y :=
    (fixedFieldEquiv F).map_add x y
  refine le_of_eq_of_le (congrArg (fun z => (fixedFieldValuation F z : ℝ)) hxy) ?_
  rcases le_max_iff.mp ((fixedFieldValuation F).map_add (fixedFieldEquiv F x) (fixedFieldEquiv F y)) with h | h
  · exact le_max_of_le_left (NNReal.coe_le_coe.mpr h)
  · exact le_max_of_le_right (NNReal.coe_le_coe.mpr h)

/-- The base embeds isometrically in the normed inertia fixed field. -/
theorem norm_algebraMap_fixedField (x : F) : ‖algebraMap F (NormedFixedField F) x‖ = ‖x‖ := by
  rw [norm_fixedField_eq, (fixedFieldEquiv F).commutes, spectralNorm_extends]

local instance : NormedAlgebra F (NormedFixedField F) where
  toAlgebra := inferInstance
  norm_smul_le r x := by rw [Algebra.smul_def, norm_mul, norm_algebraMap_fixedField]

/-- The metric completion of the actual inertia fixed field with its inherited norm. -/
abbrev CompletedField := (fixedFieldAbsoluteValue F).Completion

instance instCompletedFieldUltrametric : IsUltrametricDist (CompletedField F) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x y =>
    change ‖(x : UniformSpace.Completion (NormedFixedField F)) +
      (y : UniformSpace.Completion (NormedFixedField F))‖ ≤ _
    rw [← UniformSpace.Completion.coe_add]
    simpa only [norm_coe] using IsUltrametricDist.norm_add_le_max x y

instance instCompletedFieldNormedAlgebra : NormedAlgebra F (CompletedField F) :=
  inferInstanceAs (NormedAlgebra F (UniformSpace.Completion (NormedFixedField F)))

/-- The local field embeds isometrically in the completed maximal unramified extension. -/
theorem norm_algebraMap_completedField (x : F) : ‖algebraMap F (CompletedField F) x‖ = ‖x‖ := by
  change ‖(algebraMap F (NormedFixedField F) x : UniformSpace.Completion (NormedFixedField F))‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe, norm_algebraMap_fixedField]

instance instCompletedFieldNontrivial : NontriviallyNormedField (CompletedField F) where
  __ := (inferInstance : NormedField (UniformSpace.Completion (NormedFixedField F)))
  non_trivial := by
    obtain ⟨x, hx⟩ := (localNormedField F).non_trivial
    exact ⟨algebraMap F _ x, (norm_algebraMap_completedField F x).symm ▸ hx⟩

/-- Transport an automorphism to the normed model of the inertia fixed field. -/
def fixedFieldAut (σ : Gal(inertiaFixedField F/F)) : Gal(NormedFixedField F/F) :=
  (fixedFieldEquiv F).trans (σ.trans (fixedFieldEquiv F).symm)

private theorem fixedFieldAut_isometry (σ : Gal(inertiaFixedField F/F)) :
    Isometry (fixedFieldAut F σ) :=
  AddMonoidHomClass.isometry_of_norm (fixedFieldAut F σ) (fun x => by
    rw [norm_fixedField_eq, norm_fixedField_eq]
    unfold fixedFieldAut
    simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    exact (spectralNorm_eq_of_equiv (K := F) σ (fixedFieldEquiv F x)).symm)

/-- Extend an actual automorphism of the inertia fixed field to the normed completion. -/
def completedFieldAut (σ : Gal(inertiaFixedField F/F)) : Gal(CompletedField F/F) where
  __ := UniformSpace.Completion.mapRingEquiv (fixedFieldAut F σ).toRingEquiv
    (fixedFieldAut_isometry F σ).continuous (fixedFieldAut_isometry F σ.symm).continuous
  commutes' x := by
    change UniformSpace.Completion.mapRingHom (fixedFieldAut F σ).toRingHom
      (fixedFieldAut_isometry F σ).continuous (algebraMap F (NormedFixedField F) x) = _
    calc
      _ = ((fixedFieldAut F σ) (algebraMap F (NormedFixedField F) x) :
          UniformSpace.Completion (NormedFixedField F)) :=
        mapRingHom_coe (f := (fixedFieldAut F σ).toRingEquiv.toRingHom)
          (fixedFieldAut_isometry F σ).continuous _
      _ = _ := congrArg ((↑) : NormedFixedField F → UniformSpace.Completion (NormedFixedField F))
        ((fixedFieldAut F σ).commutes x)

@[simp]
theorem completedFieldAut_coe (σ : Gal(inertiaFixedField F/F)) (x : NormedFixedField F) :
    completedFieldAut F σ (x : UniformSpace.Completion (NormedFixedField F)) =
      (fixedFieldAut F σ x : UniformSpace.Completion (NormedFixedField F)) :=
  mapRingHom_coe (f := (fixedFieldAut F σ).toRingHom) (fixedFieldAut_isometry F σ).continuous x

/-- The automorphism on the completed field preserves the norm. -/
theorem completedFieldAut_isometry (σ : Gal(inertiaFixedField F/F)) :
    Isometry (completedFieldAut F σ) :=
  UniformSpace.Completion.isometry_mapRingHom (f := (fixedFieldAut F σ).toRingHom)
    (fixedFieldAut_isometry F σ)

set_option maxHeartbeats 500000 in
/-- The completion construction respects the multiplication of the unramified Galois group. -/
def completedFieldGaloisAction : Gal(inertiaFixedField F/F) →* Gal(CompletedField F/F) where
  toFun := completedFieldAut F
  map_one' := by
    apply AlgEquiv.ext
    intro y
    change completedFieldAut F 1 y = y
    refine UniformSpace.Completion.induction_on y ?_ fun x => ?_
    · exact isClosed_eq (completedFieldAut_isometry F 1).continuous continuous_id
    · simp [completedFieldAut_coe, fixedFieldAut]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro y
    change completedFieldAut F (σ * τ) y = completedFieldAut F σ (completedFieldAut F τ y)
    refine UniformSpace.Completion.induction_on y ?_ fun x => ?_
    · exact isClosed_eq (completedFieldAut_isometry F (σ * τ)).continuous
        ((completedFieldAut_isometry F σ).continuous.comp (completedFieldAut_isometry F τ).continuous)
    · simp [completedFieldAut_coe, fixedFieldAut, AlgEquiv.mul_apply]

/-- Arithmetic Frobenius on the completed field, extending the lift with the residue
cardinality power convention. -/
def completedFieldArithmeticFrobenius : Gal(CompletedField F/F) :=
  completedFieldGaloisAction F (exists_fixedField_arithmeticFrobenius F).choose

end Langlands.LocalGalois.Separable.UnramifiedCompletion
