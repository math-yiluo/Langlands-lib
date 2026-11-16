import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.BruhatTits.IntegralModels.ConnectedFactorization
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction

/-! # Integral split sources in neutral models of unit-fixed subsets -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- A split integral torus with a closed inclusion and a specified generic
identification with the original source torus. -/
structure UnitFixedIntegralTorusData
    (N : IntegralModel ↥𝒪[F] F G) (iS : S.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))
  isSplit : IsSplitTorus torus.toGrp
  inclusion : torus.toGrp ⟶ N.group
  closed : IsClosedSubgroup inclusion
  genericIso : (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj torus ≅ S
  generic_comm : N.genericTorusMap torus inclusion =
    CommGroupScheme.groupHom genericIso.hom ≫ iS

/-- The character-kernel fixer of a unit-fixed subset contains the image of
all units of the given source. -/
theorem unitFixedSubset_kernel_image_le
    (iS : S.toGrp ⟶ G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (Z : Set Y) (hZ : ∀ y ∈ Z, IsFixedByUnramifiedTorusUnits F iS y) :
    (characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) S.toGrp)).map
        (rationalPoints.map
          ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS)) ≤
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) Z := by
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨IntegerValuation.map_mem_characterValuationKernel
    (MaximalUnramified.valuation F) _ hs, ?_⟩
  exact (mem_fixingSubgroup_iff _).mpr fun y hy => hZ y hy s hs

/-- A split torus whose unramified units fix the subset extends into the
neutral model whenever the full model contains its character-kernel fixer. -/
theorem nonempty_unitFixedNeutralTorusData
    (iS : S.toGrp ⟶ G) (hS : IsSplitSubtorus iS)
    (N : RelativeComponentModelData ↥𝒪[F] F G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (Z : Set Y) (hZ : ∀ y ∈ Z, IsFixedByUnramifiedTorusUnits F iS y)
    (hN : characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
        fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) Z ≤
      N.full.baseChangeUnramified.integralPoints) :
    Nonempty (UnitFixedIntegralTorusData N.neutral iS) := by
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  have hv : ∀ a : (fixedFieldIntegers F)ˣ,
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) = 1 := by
    intro a
    have h := (Valuation.valuationSubring.integers (fixedFieldValuation F)).valuation_unit a
    have h' := ((MaximalUnramified.valuation_isEquiv F).eq_iff).mpr
      (h.trans (map_one (fixedFieldValuation F)).symm)
    simpa only [map_one] using h'
  obtain ⟨H, j, e, hH, hj, hgen⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange
      N.full (fixedFieldIntegers F) (inertiaFixedField F)
      (MaximalUnramified.valuation F) hv
      (fun x hx => (IntegralModel.unramifiedIntegerRange_intersection x).mp hx)
      iS hS.1 hS.2 ((unitFixedSubset_kernel_image_le iS Z hZ).trans hN)
  let : GeometricallyConnected H.toGrp.X.hom := hH.isReductive.geometricallyConnected
  let j' := RelativeIdentityComponent.factor j N.isRelativeComponent
  have hcomp : j' ≫ N.inclusion.hom = j :=
    RelativeIdentityComponent.factor_comp j N.isRelativeComponent
  have hj' : IsClosedSubgroup j' :=
    N.isRelativeComponent.isClosedSubgroup_of_comp (hcomp ▸ hj)
  refine ⟨⟨H, hH, j', hj', e, ?_⟩⟩
  rw [← hgen]
  unfold IntegralModel.genericTorusMap
  have h := N.inclusion.generic_comm
  rw [Category.comp_id] at h
  rw [← h, ← Category.assoc, ← Functor.map_comp, hcomp]

/-- Choose the closed split source in the recovered neutral model. -/
def unitFixedNeutralTorusData
    (iS : S.toGrp ⟶ G) (hS : IsSplitSubtorus iS)
    (N : RelativeComponentModelData ↥𝒪[F] F G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (Z : Set Y) (hZ : ∀ y ∈ Z, IsFixedByUnramifiedTorusUnits F iS y)
    (hN : characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
        fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) Z ≤
      N.full.baseChangeUnramified.integralPoints) :
    UnitFixedIntegralTorusData N.neutral iS :=
  Classical.choice (nonempty_unitFixedNeutralTorusData iS hS N Z hZ hN)

end Langlands.Geometry.Building
