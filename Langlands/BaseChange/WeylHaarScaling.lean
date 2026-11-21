import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.HarmonicAnalysis.GeneralHaarScalingProof
import Langlands.LocalField.ResidueNormalization
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Residue-normalized determinant scaling for additive Haar -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.BaseChange

universe u v

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue-normalized absolute value with nonnegative real codomain. -/
def residueAbsoluteNNReal : F →*₀ ℝ≥0 where
  toFun x := ⟨LocalField.residueNormalizedAbsoluteValue F x,
    (LocalField.residueNormalizedAbsoluteValue F).nonneg x⟩
  map_zero' := Subtype.ext (map_zero (LocalField.residueNormalizedAbsoluteValue F))
  map_one' := Subtype.ext (map_one (LocalField.residueNormalizedAbsoluteValue F))
  map_mul' x y := Subtype.ext (map_mul (LocalField.residueNormalizedAbsoluteValue F) x y)

private theorem uniformizer_isUniformizingElement :
    GeneralLinear.Iwasawa.IsUniformizingElement (ValuativeRel.valuation F)
      (Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)) := by
  let v := FML.normalizedMultiplicativeValuation F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let π := LocalField.uniformizer F
  have hπ0 : π ≠ 0 := LocalField.uniformizer_ne_zero F
  have hπ : v π = WithZero.exp (-1) := by
    have h := LocalField.ord_uniformizer F
    rw [FML.ord_of_ne_zero F hπ0] at h
    change ((-WithZero.log (v π) : ℤ) : WithTop ℤ) = (1 : WithTop ℤ) at h
    have hlog : WithZero.log (v π) = -1 := by
      norm_cast at h
      omega
    rw [← WithZero.exp_log (v.ne_zero_iff.mpr hπ0), hlog]
  constructor
  · change ValuativeRel.valuation F π < 1
    apply e.strictMono.lt_iff_lt.mp
    rw [map_one]
    change v π < 1
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · intro x hx
    refine ⟨-WithZero.log (v x), ?_⟩
    apply e.injective
    rw [map_zpow₀]
    change v x = v π ^ (-WithZero.log (v x))
    rw [hπ, ← WithZero.exp_zsmul]
    simpa using (WithZero.exp_log (v.ne_zero_iff.mpr hx)).symm

/-- Scalar additive Haar change of variables with the residue normalization. -/
theorem map_mul_residueAbsolute [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ] (x : F) (hx : x ≠ 0) :
    μ.map (fun y => x * y) = (residueAbsoluteNNReal F x)⁻¹ • μ := by
  let π := Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)
  have hπ : LocalField.residueNormalizedAbsoluteValue F (π : F) =
      (LocalField.residueCardinality F : ℝ)⁻¹ := by
    simpa only [π, Units.val_mk0, zpow_neg, zpow_one] using
      LocalField.residueNormalizedAbsoluteValue_uniformizer F
  have hunit (y : F) (hy : ValuativeRel.valuation F y = 1) :
      LocalField.residueNormalizedAbsoluteValue F y = 1 := by
    have hy0 : y ≠ 0 := (ValuativeRel.valuation F).ne_zero_iff.mp (by rw [hy]; exact one_ne_zero)
    let u := Units.mk0 y hy0
    have hu : u ∈ FML.unitGroup F := by
      rw [Valuation.mem_unitGroup_iff]
      exact hy
    exact LocalField.residueNormalizedAbsoluteValue_unit F u hu
  exact Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement F
    (LocalField.residueCardinality F) rfl (LocalField.residueNormalizedAbsoluteValue F)
    π (uniformizer_isUniformizingElement F) hπ hunit μ (Units.mk0 x hx)

/-- A continuous linear automorphism on a finite-dimensional space scales
additive Haar by the inverse residue-normalized determinant. -/
abbrev ResidueNormalizedHaarScalingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul F X] [T2Space X]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsAddHaarMeasure μ] (L : X ≃L[F] X),
    μ.map L = (residueAbsoluteNNReal F L.toLinearEquiv.toLinearMap.det)⁻¹ • μ

theorem map_linearEquiv_residueAbsolute : ResidueNormalizedHaarScalingStatement.{u, v} := by
  intro F _ _ _ _ X _ _ _ _ _ _ _ _ _ _ _ μ _ L
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  let : SecondCountableTopology F := HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let b := Module.finBasis F X
  let e := b.equivFun.toContinuousLinearEquiv
  let L' := e.toLinearEquiv.conj L.toLinearEquiv.toLinearMap
  let M := LinearMap.toMatrix' L'
  have hdet : M.det = L.toLinearEquiv.toLinearMap.det := by
    have h := LinearMap.det_conj L.toLinearEquiv.toLinearMap e.toLinearEquiv
    rw [← LinearMap.comp_assoc, ← LinearEquiv.conj_apply] at h
    exact (LinearMap.det_toMatrix' L').trans h
  have hM : M.det ≠ 0 := hdet ▸ L.toLinearEquiv.isUnit_det'.ne_zero
  have hlin : Matrix.toLin' M = L' :=
    (LinearMap.toMatrix' : _ ≃ₗ[F] _).symm_apply_apply L'
  have he : (fun x => e.symm (Matrix.toLin' M (e x))) = (L : X → X) := by
    rw [hlin]
    funext x
    change e.symm (e (L (e.symm (e x)))) = L x
    rw [e.symm_apply_apply, e.symm_apply_apply]
  have hμ := HarmonicAnalysis.haarMeasure_map_in_coordinates (addHaar : Measure F)
    (residueAbsoluteNNReal F) (map_mul_residueAbsolute F addHaar) e.toContinuousAddEquiv μ hM
  rw [hdet] at hμ
  change μ.map (fun x => e.symm (Matrix.toLin' M (e x))) = _ at hμ
  rwa [he] at hμ

end Langlands.BaseChange
