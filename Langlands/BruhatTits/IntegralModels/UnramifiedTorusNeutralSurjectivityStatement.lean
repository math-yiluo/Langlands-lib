import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.AbelianScheme.Kernel

/-! # Surjectivity on neutral integral points of an exact sequence of tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Corollary B.8.6 over the maximal unramified extension.**
For a surjective homomorphism of tori with torus kernel, each neutral integral
point of a smooth maximal-bounded model of the target lifts to a neutral
integral point of a smooth maximal-bounded model of the source.
The full models and their actual relative identity components are supplied. -/
def UnramifiedTorusNeutralSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (B C : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine B.X.left] [IsAffine C.X.left],
    IsTorus B.toGrp → IsTorus C.toGrp →
    ∀ q : B.toGrp ⟶ C.toGrp,
      Surjective q.hom.hom.left → IsTorus (kernel q) →
      ∀ (DB : RelativeComponentModelData
          (fixedFieldIntegers F) (inertiaFixedField F) B.toGrp)
        (DC : RelativeComponentModelData
          (fixedFieldIntegers F) (inertiaFixedField F) C.toGrp),
        DB.full.integralPoints =
            characterValuationKernel (fixedFieldValuation F) B.toGrp →
        DC.full.integralPoints =
            characterValuationKernel (fixedFieldValuation F) C.toGrp →
        DC.neutral.integralPoints ≤
          DB.neutral.integralPoints.map (rationalPoints.map q)

end Langlands.BruhatTits.IntegralModels
