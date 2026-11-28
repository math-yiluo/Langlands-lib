import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Langlands.Representation.Plancherel.SplitTorusCompactUnits
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Finite-image scalar characters after a unitary twist -/

noncomputable section

namespace Langlands.JacquetLanglands

open Plancherel

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (D : Type u) [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [TopologicalSpace D] [IsModuleTopology F D]

/-- The order of the determinant of left multiplication by a division unit. -/
def divisionNormOrder : Dˣ →* Multiplicative ℤ :=
  (fieldOrderUnits F).comp (Units.map (Algebra.norm F : D →* F))

omit [TopologicalSpace D] [IsModuleTopology F D] in
theorem divisionNormOrder_scalar (a : Fˣ) :
    divisionNormOrder F D (Units.map (algebraMap F D).toMonoidHom a) =
      fieldOrderUnits F a ^ Module.finrank F D := by
  have h : Units.map (Algebra.norm F : D →* F)
      (Units.map (algebraMap F D).toMonoidHom a) = a ^ Module.finrank F D := by
    apply Units.ext
    change Algebra.norm F (algebraMap F D (a : F)) =
      ((a ^ Module.finrank F D : Fˣ) : F)
    rw [Units.val_pow_eq_pow_val, Algebra.norm_algebraMap]
  rw [divisionNormOrder, MonoidHom.comp_apply, h, map_pow]

include F in
/-- The order of the determinant of a division unit is locally constant. -/
theorem divisionNormOrder_isLocallyConstant : IsLocallyConstant (divisionNormOrder F D) := by
  have hn : Continuous (Algebra.norm F : D → F) := by
    let b := Module.finBasis F D
    have hM : Continuous (Algebra.leftMulMatrix b) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
    exact hM.matrix_det.congr (fun a => (Algebra.norm_eq_matrix_det b a).symm)
  exact (fieldOrderUnits_isLocallyConstant F).comp_continuous
    (hn.units_map (Algebra.norm F : D →* F))

private theorem finite_range_of_valuation_one (π : Fˣ)
    (hπ : fieldOrderUnits F π = Multiplicative.ofAdd 1) (ω : Fˣ →* ℂˣ)
    (hω : IsLocallyConstant ω) (hωπ : ω π = 1) : (Set.range ω).Finite := by
  let K := (fieldOrderUnits F).ker
  have hK : IsCompact (K : Set Fˣ) := by
    change IsCompact ((fieldOrderUnits F).ker : Set Fˣ)
    rw [fieldOrderUnits_ker]
    exact SplitTorus.isCompact_fieldUnitGroup F
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (hω.comp_continuous (continuous_subtype_val (p := (· ∈ K)))).range_finite.subset
  rintro _ ⟨a, rfl⟩
  let k := (fieldOrderUnits F a).toAdd
  have h : a * π ^ (-k) ∈ K := by
    change fieldOrderUnits F (a * π ^ (-k)) = 1
    rw [map_mul, map_zpow, hπ]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, Int.toAdd_zpow]
    change k + 1 * (-k) = 0
    rw [one_mul, add_neg_cancel]
  refine ⟨⟨_, h⟩, ?_⟩
  change ω (a * π ^ (-k)) = ω a
  rw [map_mul, map_zpow, hωπ, one_zpow, mul_one]

/-- A smooth unitary scalar character of a division group acquires finite image after
a smooth unitary twist through the valuation of the determinant of left multiplication. -/
theorem exists_unitaryTwist_finite_range (ω : Fˣ →* ℂˣ)
    (hω : IsLocallyConstant ω) (hu : ∀ a, ‖(ω a : ℂ)‖ = 1) :
    ∃ χ : Dˣ →* ℂˣ, IsLocallyConstant χ ∧ (∀ g, ‖(χ g : ℂ)‖ = 1) ∧
      (Set.range (ω * χ.comp (Units.map (algebraMap F D).toMonoidHom))).Finite := by
  obtain ⟨π, hπ⟩ := fieldOrderUnits_surjective F (Multiplicative.ofAdd 1)
  let d := Module.finrank F D
  have hd : 0 < d := Module.finrank_pos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((ω π : ℂ)⁻¹) hd
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hx
    exact (inv_ne_zero (Units.ne_zero (ω π))) hx.symm
  have hxnorm : ‖x‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, norm_inv, hu, inv_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hd.ne').mp h
  let w : ℂˣ := Units.mk0 x hx0
  let e : Multiplicative ℤ →* ℂˣ :=
    { toFun := fun m => w ^ m.toAdd
      map_one' := zpow_zero w
      map_mul' := fun a b => zpow_add w a.toAdd b.toAdd }
  let χ := e.comp (divisionNormOrder F D)
  have hχ : IsLocallyConstant χ := (divisionNormOrder_isLocallyConstant F D).comp e
  let i := Units.map (algebraMap F D).toMonoidHom
  have := IsModuleTopology.toContinuousAdd F D
  have hi : Continuous i :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F D)).units_map
      (algebraMap F D).toMonoidHom
  have hχπ : χ (i π) = w ^ d := by
    change w ^ (divisionNormOrder F D (i π)).toAdd = _
    rw [divisionNormOrder_scalar, hπ, Int.toAdd_pow]
    change w ^ (1 * (d : ℤ)) = w ^ d
    rw [one_mul, zpow_natCast]
  refine ⟨χ, hχ, ?_, finite_range_of_valuation_one F π hπ (ω * χ.comp i)
    (hω.comp₂ (hχ.comp_continuous hi) (· * ·)) ?_⟩
  · intro g
    change ‖((w ^ (divisionNormOrder F D g).toAdd : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, Units.val_mk0, hxnorm, one_zpow]
  · rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχπ]
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hx,
      mul_inv_cancel₀ (Units.ne_zero (ω π)), Units.val_one]

end Langlands.JacquetLanglands
