import Langlands.Automorphic.GroupSchemeFullAEL2Hilbert
import Langlands.Automorphic.GroupSchemeFullAEL2Continuity
import Langlands.Automorphic.GroupSchemeQuotientL2Integrated

/-! # Bochner integration on the original full AE cuspidal L2 space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ρ" => quotientL2RightAction F G T i μQ hR
local notation "ρc" => fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc

/-- Bundle the original full cusp representation by the bounded maps of its isometries. -/
def fullAEL2CuspidalBoundedRightAction : AdelicGroupPoints F G →* (S →L[ℂ] S) where
  toFun a :=
    (fullAEL2CuspidalRightTranslate F G hPD hG T i hi I e hc a).toLinearIsometry.toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact quotientL2RightTranslate_one F G T i μQ hR φ.val
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact quotientL2RightTranslate_mul F G T i μQ hR a b φ.val

@[simp]
theorem fullAEL2CuspidalBoundedRightAction_apply (a : AdelicGroupPoints F G) (φ : S) :
    fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc a φ = ρc a φ := rfl

theorem norm_fullAEL2CuspidalBoundedRightAction (a : AdelicGroupPoints F G) (φ : S) :
    ‖fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc a φ‖ = ‖φ‖ :=
  norm_fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc a φ

local notation "πc" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
local notation "hπcnorm" => norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc

variable (ν : Measure (AdelicGroupPoints F G))

/-- Actual continuous cusp orbits are strongly measurable for the specified group measure. -/
theorem fullAEL2CuspidalOrbit_aestronglyMeasurable (φ : S) :
    AEStronglyMeasurable (fun a => πc a φ) ν :=
  (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc φ).continuous.stronglyMeasurable.aestronglyMeasurable

local notation "hπcmeas" =>
  fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG T i hi I e hc ν

variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

include hf in
/-- The original weighted cusp orbit has an absolutely convergent Bochner integral. -/
theorem fullAEL2CuspidalActionIntegrand_integrable (φ : S) :
    Integrable (fun a => f a • ρc a φ) ν :=
  isometricActionIntegrand_integrable ν πc hπcnorm hπcmeas f hf φ

/-- Integrate the unchanged action inside the actual complete full cusp carrier. -/
def fullAEL2CuspidalIntegratedAction : S →L[ℂ] S :=
  integratedIsometricAction ν πc hπcnorm hπcmeas f hf

@[simp]
theorem fullAEL2CuspidalIntegratedAction_apply (φ : S) :
    fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf φ =
      ∫ a, f a • ρc a φ ∂ν := rfl

theorem norm_fullAEL2CuspidalIntegratedAction_le :
    ‖fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf‖ ≤
      ∫ a, ‖f a‖ ∂ν :=
  integratedIsometricAction_norm_le ν πc hπcnorm hπcmeas f hf

/-- The actual faithful inclusion identifies the cusp and ambient orbit integrals. -/
theorem fullAEL2CuspidalIntegratedAction_val (φ : S) :
    (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf φ).val =
      haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ.val := by
  exact ((fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc).integral_comp_comm
    (fun a => f a • ρc a φ)).symm

/-- The ambient integrated operator preserves the original all-parabolic cusp submodule. -/
theorem haarQuotientL2IntegratedAction_mem_fullAEL2CuspidalSubmodule
    (φ : Lp ℂ 2 μQ) (hφ : φ ∈ S) :
    haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ ∈ S := by
  rw [← fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc ν f hf ⟨φ, hφ⟩]
  exact (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf ⟨φ, hφ⟩).property

/-- The original subtype-valued orthogonal projection commutes with Bochner integration. -/
theorem fullAEL2CuspidalOrthogonalProjection_integratedAction (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc
      (haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ) =
        fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf
          (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ) := by
  let P := fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc
  change P (∫ a, f a • ρ a φ ∂ν) = ∫ a, f a • ρc a (P φ) ∂ν
  rw [← P.integral_comp_comm
    (haarQuotientL2ActionIntegrand_integrable F G T i hi I e hc ν f hf φ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    change P (f a • ρ a φ) = f a • ρc a (P φ)
    rw [map_smul]
    exact congrArg (fun ψ => f a • ψ)
      (fullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG T i hi I e hc a φ)

/-- The original ambient orthogonal projection also commutes with the integrated operator. -/
theorem fullAEL2CuspidalAmbientProjection_integratedAction (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc
      (haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ) =
        haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf
          (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ) := by
  have h := congrArg (fun ψ : S => ψ.val)
    (fullAEL2CuspidalOrthogonalProjection_integratedAction F G hPD hG T i hi I e hc ν f hf φ)
  exact h.trans (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc ν f hf _)

end Langlands.Automorphic.GroupSchemeFunctions
