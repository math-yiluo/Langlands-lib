import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Finite generation of torus points modulo neutral integral points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **Torus points modulo neutral integral points are finitely generated.**
For a torus `T` over the maximal unramified extension `K` of a nonarchimedean
local field and supplied relative-component model data whose full integral
points are the character-valuation kernel `T(K)^1`, finitely many points of
`T(K)` together with the neutral integral points generate `T(K)`. -/
def UnramifiedTorusNeutralFiniteGenerationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))),
    IsTorus T →
    ∀ D : RelativeComponentModelData
        (fixedFieldIntegers F) (inertiaFixedField F) T,
      D.full.integralPoints =
          characterValuationKernel (fixedFieldValuation F) T →
      ∃ s : Set (rationalPoints T), s.Finite ∧
        Subgroup.closure s ⊔ D.neutral.integralPoints = ⊤

end Langlands.BruhatTits.IntegralModels
