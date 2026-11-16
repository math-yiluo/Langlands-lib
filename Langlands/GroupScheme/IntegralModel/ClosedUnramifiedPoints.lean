import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.IntegralModel.SchematicClosure
import Langlands.GroupScheme.LocalUnramifiedTwistDescent

/-! # Integral coordinates through a closed model over the unramified extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison
open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {U G : GroupScheme (Spec (CommRingCat.of F))}
  {M : IntegralModel ↥𝒪[F] F U} {N : IntegralModel ↥𝒪[F] F G} {q : U ⟶ G}

local instance closedUnramifiedPointsIntegerAlgebra :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance closedUnramifiedPointsIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Integral coordinates in a closed integral subgroup are exactly ambient
integrality of its image, on every point over the maximal unramified extension. -/
theorem hasIntegralCoordinates_iff_map_mem_baseChangeUnramified
    (φ : M.Hom N q) (hφ : IsClosedSubgroup φ.hom)
    (x : rationalPoints (baseChanged F (UnramifiedClosure F) U)) :
    M.HasIntegralCoordinates (UnramifiedClosure F)
        (baseChangeCoeffEquiv F (UnramifiedClosure F) U x) ↔
      rationalPoints.map
          ((GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map q) x ∈
        N.baseChangeUnramified.integralPoints := by
  rw [← M.mem_baseChangeUnramified_integralPoints_iff]
  simp only [MulEquiv.symm_apply_apply]
  have hclosed : IsClosedSubgroup
      (φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).hom :=
    φ.isClosedImmersion_baseChangeCoefficients _ _ hφ
  change x ∈ (M.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).integralPoints ↔ _
  rw [(φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).integralPoints_eq_comap
    hclosed]
  rfl

end Langlands.GroupScheme.IntegralModel
