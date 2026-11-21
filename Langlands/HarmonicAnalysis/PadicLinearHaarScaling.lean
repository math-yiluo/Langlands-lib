import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Determinant scaling of additive Haar in a finite p-adic vector space. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Langlands.GeneralLinear
open scoped NNReal

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance linearHaarFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance linearHaarFieldValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance linearHaarFieldLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance linearHaarFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance linearHaarFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance linearHaarFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance linearHaarFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- Every invertible linear endomorphism of a finite-dimensional p-adic vector space
pushes its additive Haar measure to inverse absolute determinant times that measure. -/
theorem padicLinearHaarScaling {W : Type v} [AddCommGroup W] [Module F.Carrier W]
    [Module.Finite F.Carrier W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [IsModuleTopology F.Carrier W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) [μ.IsAddHaarMeasure] (f : Module.End F.Carrier W)
    (hf : f.det ≠ 0) :
    Measure.map f μ = (F.canonicalTopologicalData.normalizedAbsHom f.det)⁻¹ • μ := by
  let T := F.canonicalTopologicalData
  let b := Module.finBasis F.Carrier W
  let e : W ≃ₜ+ (Fin (Module.finrank F.Carrier W) → F.Carrier) :=
    { toAddEquiv := b.equivFun.toAddEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  let M := LinearMap.toMatrix b b f
  have hDet : M.det = f.det := LinearMap.det_toMatrix b f
  have hScale (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have h := haarMeasure_map_in_coordinates Measure.addHaar T.normalizedAbsHom hScale e μ
    (M := M) (hDet.symm ▸ hf)
  have hMap : (fun x => e.symm (Matrix.toLin' M (e x))) = ⇑f := by
    funext x
    apply e.injective
    rw [ContinuousAddEquiv.apply_symm_apply]
    change Matrix.toLin' (LinearMap.toMatrix b b f) (b.equivFun x) = b.equivFun (f x)
    rw [Matrix.toLin'_apply, b.equivFun_apply, b.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  rwa [hMap, hDet] at h

end Langlands.HarmonicAnalysis
