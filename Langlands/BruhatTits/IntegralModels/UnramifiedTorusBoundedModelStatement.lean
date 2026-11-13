import Langlands.GroupScheme.IntegralModel
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Smooth models of the maximal bounded torus subgroup over the unramified integers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Proposition B.7.2(2) and Corollary B.7.4 over the maximal unramified
extension.** For every torus `T` over `K = inertiaFixedField F`, its maximal
bounded subgroup `T(K)^1`, the common kernel of the valuations of the rational
characters, is the integral-point image of a smooth affine model over
`fixedFieldIntegers F`. -/
def UnramifiedTorusBoundedModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left],
    IsTorus T.toGrp →
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp,
      M.IsSmooth ∧
        M.integralPoints = characterValuationKernel (fixedFieldValuation F) T.toGrp

end Langlands.BruhatTits.IntegralModels
