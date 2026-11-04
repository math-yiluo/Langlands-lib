import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothSheafTrace
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTrace

/-! # Smooth full coefficient traces for actual rational subgroup restriction -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology Opposite
open Langlands.Sheaf.Equivariant Langlands.LocallyConstantCovering
open scoped BigOperators

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable {U V : OpenSubgroup G} (h : V ≤ U) (d : ρ.InvariantRationalDomain U)
  [targetStable : HasStableNeighbourhoods ((inclusion U).obj d).subgroup.toSubgroup
    ((inclusion U).obj d).LocalSpectrum]

include targetStable in
/-- Restrict actual stable neighbourhoods using the original subgroup inclusion. -/
theorem subgroupRestriction_hasStableNeighbourhoods :
    HasStableNeighbourhoods
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).subgroup.toSubgroup
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).LocalSpectrum where
  exists_stable x O hO hx := by
    obtain ⟨H, W, hW, hxW, hWO, hHW⟩ :=
      targetStable.exists_stable x O hO hx
    let i := Subgroup.inclusion (show V.toSubgroup ≤ U.toSubgroup from h)
    have hi : Continuous i := continuous_subtype_val.subtype_mk _
    refine ⟨H.comap i hi, W, hW, hxW, hWO, ?_⟩
    intro v hv y hy
    exact hHW (i v) hv y hy

include targetStable in
local instance sourceStable :
    HasStableNeighbourhoods
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).subgroup.toSubgroup
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).LocalSpectrum :=
  subgroupRestriction_hasStableNeighbourhoods h d

variable (R : Type u) [CommRing R]

/-- Smooth pullback retains the full original coefficients on the actual subgroup map. -/
def subgroupRestrictionSmoothCoefficientMap (M : SmoothRep.{u, u, u} R G) :
    (SmoothSheafVariation.coefficientFunctor R ((inclusion U).obj d)).obj M ⟶
      (SmoothSheafVariation.directImage R (subgroupRestriction h d)).obj
        ((SmoothSheafVariation.coefficientFunctor R
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).obj M) :=
  SmoothSheafVariation.coefficientMap R (subgroupRestriction h d) M

/-- Pullback naturality uses every original smooth coefficient intertwiner. -/
def subgroupRestrictionSmoothCoefficientNatTrans :
    SmoothSheafVariation.coefficientFunctor R ((inclusion U).obj d) ⟶
      SmoothSheafVariation.coefficientFunctor R
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) ⋙
        SmoothSheafVariation.directImage R (subgroupRestriction h d) :=
  SmoothSheafVariation.coefficientNatTrans R (subgroupRestriction h d)

@[simp]
theorem subgroupRestrictionSmoothCoefficientNatTrans_app (M : SmoothRep.{u, u, u} R G) :
    (subgroupRestrictionSmoothCoefficientNatTrans h d R).app M =
      subgroupRestrictionSmoothCoefficientMap h d R M := rfl

@[reassoc (attr := simp)]
theorem subgroupRestrictionSmoothCoefficientMap_inclusion
    (M : SmoothRep.{u, u, u} R G) :
    (Langlands.Sheaf.Equivariant.smoothInclusion R G
      ((inclusion U).obj d).InducedSpectrum).map
        (subgroupRestrictionSmoothCoefficientMap h d R M) ≫
      (SmoothSheafVariation.inclusion R (subgroupRestriction h d)).app
        ((SmoothSheafVariation.coefficientFunctor R
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).obj M) =
      SheafVariation.coefficientMap (subgroupRestriction h d) M.representation := rfl

section Trace

variable [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

local instance finite_subgroupRestrictionSmoothFiber :
    ∀ y, Finite ((subgroupRestriction h d).inducedMap ⁻¹' {y}) :=
  finite_subgroupRestriction_inducedMap_fiber h d

/-- The original finite-index subgroup covering gives the actual smooth sheaf trace. -/
def subgroupRestrictionSmoothCoefficientTrace (M : SmoothRep.{u, u, u} R G) :
    (SmoothSheafVariation.directImage R (subgroupRestriction h d)).obj
        ((SmoothSheafVariation.coefficientFunctor R
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).obj M) ⟶
      (SmoothSheafVariation.coefficientFunctor R ((inclusion U).obj d)).obj M :=
  SmoothSheafVariation.coefficientTrace R (subgroupRestriction h d)
    (isCoveringMap_subgroupRestriction_inducedMap h d) M

/-- Forgetting smoothness gives inclusion followed by the unchanged full subgroup trace. -/
@[simp]
theorem subgroupRestrictionSmoothCoefficientTrace_forget
    (M : SmoothRep.{u, u, u} R G) :
    (Langlands.Sheaf.Equivariant.smoothInclusion R G
      ((inclusion U).obj d).InducedSpectrum).map
        (subgroupRestrictionSmoothCoefficientTrace h d R M) =
      (SmoothSheafVariation.inclusion R (subgroupRestriction h d)).app
          ((SmoothSheafVariation.coefficientFunctor R
            ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).obj M) ≫
        subgroupRestrictionCoefficientTrace h d M.representation := rfl

/-- Trace evaluates the original underlying inverse-open section. -/
@[simp]
theorem subgroupRestrictionSmoothCoefficientTrace_apply
    (M : SmoothRep.{u, u, u} R G)
    (A : ActionOpens G ((inclusion U).obj d).InducedSpectrum)
    (s : ((SmoothSheafVariation.directImage R (subgroupRestriction h d)).obj
      ((SmoothSheafVariation.coefficientFunctor R
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).obj M)).obj.obj.obj
          (op A))
    (y : A.openSet) :
    LocallyConstant.toFun
        (((subgroupRestrictionSmoothCoefficientTrace h d R M).hom.hom.app (op A)).hom s)
          y =
      fiberSum (DirectImage.pointMap (subgroupRestriction h d).inducedMap
        (subgroupRestriction h d).inducedMap_smul A)
          (LocallyConstant.toFun (s.val :
            LocallyConstant ((SheafVariation.preimage (subgroupRestriction h d)).obj A).openSet
              M)) y := rfl

/-- The sum indexes all actual relative cosets and hence the whole original fiber. -/
theorem subgroupRestrictionSmoothCoefficientTrace_apply_sum
    (M : SmoothRep.{u, u, u} R G)
    (A : ActionOpens G ((inclusion U).obj d).InducedSpectrum)
    (s : ((SmoothSheafVariation.directImage R (subgroupRestriction h d)).obj
      ((SmoothSheafVariation.coefficientFunctor R
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).obj M)).obj.obj.obj
          (op A))
    (y : A.openSet) [Fintype (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)] :
    LocallyConstant.toFun
        (((subgroupRestrictionSmoothCoefficientTrace h d R M).hom.hom.app (op A)).hom s)
          y =
      ∑ c : U ⧸ V.toSubgroup.subgroupOf U.toSubgroup,
        (LocallyConstant.toFun (s.val :
          LocallyConstant ((SheafVariation.preimage (subgroupRestriction h d)).obj A).openSet
            M)) ⟨(subgroupRestrictionFiberHomeomorph h d y.val c).val, by
              change (subgroupRestriction h d).inducedMap
                (subgroupRestrictionFiberHomeomorph h d y.val c).val ∈ A.openSet
              rw [show (subgroupRestriction h d).inducedMap
                (subgroupRestrictionFiberHomeomorph h d y.val c).val = y.val from
                  (subgroupRestrictionFiberHomeomorph h d y.val c).property]
              exact y.property⟩ := by
  exact fiberSum_eq_sum _ _ _
    ((subgroupRestrictionFiberHomeomorph h d y.val).toEquiv.trans
      (DirectImage.pointMapFiberEquiv (subgroupRestriction h d).inducedMap
        (subgroupRestriction h d).inducedMap_smul A y).symm)

/-- Smooth pullback followed by trace has the proved actual relative-index degree. -/
theorem subgroupRestrictionSmoothCoefficientTrace_pullback_apply
    (M : SmoothRep.{u, u, u} R G)
    (A : ActionOpens G ((inclusion U).obj d).InducedSpectrum)
    (s : LocallyConstant A.openSet M) (y : A.openSet) :
    LocallyConstant.toFun
        (((subgroupRestrictionSmoothCoefficientMap h d R M ≫
          subgroupRestrictionSmoothCoefficientTrace h d R M).hom.hom.app (op A)).hom s) y =
      V.toSubgroup.relIndex U.toSubgroup • s y := by
  change LocallyConstant.toFun
    (((SmoothSheafVariation.coefficientMap R (subgroupRestriction h d) M ≫
      SmoothSheafVariation.coefficientTrace R (subgroupRestriction h d)
        (isCoveringMap_subgroupRestriction_inducedMap h d) M).hom.hom.app (op A)).hom s) y = _
  rw [SmoothSheafVariation.coefficientTrace_pullback_apply,
    card_subgroupRestriction_inducedMap_fiber]

/-- The finite-index trace is natural on the entire original smooth coefficient category. -/
def subgroupRestrictionSmoothCoefficientTraceNatTrans :
    SmoothSheafVariation.coefficientFunctor R
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) ⋙
      SmoothSheafVariation.directImage R (subgroupRestriction h d) ⟶
        SmoothSheafVariation.coefficientFunctor R ((inclusion U).obj d) :=
  SmoothSheafVariation.coefficientTraceNatTrans R (subgroupRestriction h d)
    (isCoveringMap_subgroupRestriction_inducedMap h d)

@[simp]
theorem subgroupRestrictionSmoothCoefficientTraceNatTrans_app
    (M : SmoothRep.{u, u, u} R G) :
    (subgroupRestrictionSmoothCoefficientTraceNatTrans h d R).app M =
      subgroupRestrictionSmoothCoefficientTrace h d R M := rfl

@[reassoc]
theorem subgroupRestrictionSmoothCoefficientTrace_naturality
    {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (SmoothSheafVariation.directImage R (subgroupRestriction h d)).map
        ((SmoothSheafVariation.coefficientFunctor R
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))).map a) ≫
        subgroupRestrictionSmoothCoefficientTrace h d R N =
      subgroupRestrictionSmoothCoefficientTrace h d R M ≫
        (SmoothSheafVariation.coefficientFunctor R ((inclusion U).obj d)).map a :=
  (subgroupRestrictionSmoothCoefficientTraceNatTrans h d R).naturality a

end Trace

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
