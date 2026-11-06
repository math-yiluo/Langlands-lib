import Langlands.Automorphic.GroupSchemeQuotientL2Continuity
import Langlands.Representation.Unitary.IntegratedOperator

/-! # Bochner integration of the original canonical quotient L2 action -/

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
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ρ" => quotientL2RightAction F G T i μQ hR

/-- The original positive right representation, bundled by bounded linear maps. -/
def haarQuotientL2BoundedRightAction :
    AdelicGroupPoints F G →* (Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ) where
  toFun a := (quotientL2RightTranslate F G T i μQ hR a).toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    exact quotientL2RightTranslate_one F G T i μQ hR
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    exact quotientL2RightTranslate_mul F G T i μQ hR a b

@[simp]
theorem haarQuotientL2BoundedRightAction_apply (a : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) :
    haarQuotientL2BoundedRightAction F G T i hi I e hc a φ = ρ a φ := rfl

theorem norm_haarQuotientL2BoundedRightAction (a : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) :
    ‖haarQuotientL2BoundedRightAction F G T i hi I e hc a φ‖ = ‖φ‖ :=
  (quotientL2RightTranslate F G T i μQ hR a).norm_map φ

local notation "π" => haarQuotientL2BoundedRightAction F G T i hi I e hc
local notation "hπnorm" => norm_haarQuotientL2BoundedRightAction F G T i hi I e hc

variable (ν : Measure (AdelicGroupPoints F G))

/-- Continuous original orbits are strongly measurable for every supplied group measure. -/
theorem haarQuotientL2Orbit_aestronglyMeasurable (φ : Lp ℂ 2 μQ) :
    AEStronglyMeasurable (fun a => π a φ) ν :=
  (haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous.stronglyMeasurable.aestronglyMeasurable

local notation "hπmeas" => haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc ν

variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

include hf in
/-- Absolute Bochner convergence is proved before using the orbit integral. -/
theorem haarQuotientL2ActionIntegrand_integrable (φ : Lp ℂ 2 μQ) :
    Integrable (fun a => f a • ρ a φ) ν :=
  isometricActionIntegrand_integrable ν π hπnorm hπmeas f hf φ

/-- The actual weighted original quotient action on the unchanged L2 space. -/
def haarQuotientL2IntegratedAction : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ :=
  integratedIsometricAction ν π hπnorm hπmeas f hf

@[simp]
theorem haarQuotientL2IntegratedAction_apply (φ : Lp ℂ 2 μQ) :
    haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ =
      ∫ a, f a • ρ a φ ∂ν := rfl

theorem norm_haarQuotientL2IntegratedAction_le :
    ‖haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf‖ ≤ ∫ a, ‖f a‖ ∂ν :=
  integratedIsometricAction_norm_le ν π hπnorm hπmeas f hf

end Langlands.Automorphic.GroupSchemeFunctions
