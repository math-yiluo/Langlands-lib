import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelStatement
import Langlands.GroupScheme.IntegralModel.MaximalBounded
import Langlands.GroupScheme.Torus.Geometry
import Langlands.Geometry.Building.UnramifiedTorusNormOneBoundedness
import Langlands.Geometry.Building.IntegerValuationBoundedGeometry
import Langlands.Geometry.Building.UnramifiedStabilizerDescent

/-! # The maximal-bounded-model reduction for unramified tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The integer-normalized character kernel of an actual affine torus over the
inertia fixed field is maximal among algebraically bounded subgroups. -/
theorem maximal_characterValuationKernel
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T) :
    let := ValuativeRel.ofValuation (fixedFieldValued F).v
    Maximal (fun B : Subgroup (rationalPoints T) =>
      IsAlgebraicallyBounded (inertiaFixedField F) T.X
        (B : Set (rationalPoints T)))
      (characterValuationKernel (valuation F) T) := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let : (valuation F).Compatible := valuation_compatible F
  refine ⟨isAlgebraicallyBounded_characterValuationKernel F T hT, ?_⟩
  intro B hB _
  exact IntegerValuation.subgroup_le_characterValuationKernel_of_isAlgebraicallyBounded
    (valuation F) T B hB

/-- Equivalent valuations identify the maximal bounded torus subgroup with the
character kernel for the literal fixed-field valuation used by the model target. -/
theorem maximal_fixedFieldCharacterValuationKernel
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T) :
    let := ValuativeRel.ofValuation (fixedFieldValued F).v
    Maximal (fun B : Subgroup (rationalPoints T) =>
      IsAlgebraicallyBounded (inertiaFixedField F) T.X
        (B : Set (rationalPoints T)))
      (characterValuationKernel (fixedFieldValuation F) T) := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  rw [← characterValuationKernel_eq_of_isEquiv (valuation_isEquiv F)]
  exact maximal_characterValuationKernel F T hT

end Langlands.Geometry.Building.MaximalUnramified

namespace Langlands.BruhatTits.IntegralModels

/-- The general maximal-bounded-subgroup model theorem suffices for the smooth
bounded torus model over the actual unramified integer ring. -/
def UnramifiedTorusBoundedModelAssemblyStatement : Prop :=
  MaximalBoundedIntegralModelStatement.{u} →
    UnramifiedTorusBoundedModelStatement.{u}

/-- Prove the reduction using torus-kernel maximality and transport along the
published equality of the intrinsic and fixed-field integer rings. -/
theorem unramifiedTorusBoundedModelAssembly :
    UnramifiedTorusBoundedModelAssemblyStatement.{u} := by
  intro hmaximal F _ _ _ _ T _ hT
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  have hmodel (A : ValuationSubring (inertiaFixedField F))
      (hA : A = (ValuativeRel.valuation (inertiaFixedField F)).valuationSubring)
      [IsDiscreteValuationRing A] [HenselianLocalRing A]
      [IsAlgClosed (IsLocalRing.ResidueField A)] :
      ∃ M : IntegralModel A (inertiaFixedField F) T.toGrp,
        M.IsSmooth ∧
          M.integralPoints = characterValuationKernel (fixedFieldValuation F) T.toGrp := by
    subst A
    exact hmaximal (inertiaFixedField F) T.toGrp hT.smooth
      (characterValuationKernel (fixedFieldValuation F) T.toGrp)
      (MaximalUnramified.maximal_fixedFieldCharacterValuationKernel F T.toGrp hT)
  exact hmodel (fixedFieldIntegers F) (fixedFieldIntrinsicIntegers_eq F).symm

end Langlands.BruhatTits.IntegralModels
