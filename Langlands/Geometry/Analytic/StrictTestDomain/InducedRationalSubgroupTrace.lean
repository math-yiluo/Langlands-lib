import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupCovering
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSheafTrace
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCorrespondence
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalProperTransport

/-! # Actual finite-subgroup-restriction coefficient traces -/

noncomputable section

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology Opposite
open Langlands.Sheaf.Equivariant Langlands.LocallyConstantCovering
open scoped BigOperators

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport

variable {U V : OpenSubgroup G} (h : V ≤ U) (d : ρ.InvariantRationalDomain U)
  [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

local instance finite_subgroupRestrictionFiber :
    ∀ y, Finite ((subgroupRestriction h d).inducedMap ⁻¹' {y}) :=
  finite_subgroupRestriction_inducedMap_fiber h d

/-- The unchanged original subgroup arrow belongs to the actual proper category. -/
def properSubgroupRestriction :
    (⟨(inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)⟩ : ProperTransport ρ) ⟶
      (⟨(inclusion U).obj d⟩ : ProperTransport ρ) :=
  ⟨subgroupRestriction h d, isProperMap_subgroupRestriction_inducedMap h d⟩

@[simp]
theorem properSubgroupRestriction_hom :
    (properSubgroupRestriction h d).hom = subgroupRestriction h d := rfl

section Sheaf

variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Trace on every original coefficient sheaf, with covering and fibers proved. -/
def subgroupRestrictionCoefficientTrace (τ : Representation R G M) :
    (SheafVariation.directImage (ModuleCat.{max (max u v) w} R)
        (subgroupRestriction h d)).obj
        (LocallyConstantSheaf.sheaf
          (X := ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).InducedSpectrum)
          τ) ⟶
      LocallyConstantSheaf.sheaf (X := ((inclusion U).obj d).InducedSpectrum) τ :=
  SheafVariation.coefficientTrace (subgroupRestriction h d)
    (isCoveringMap_subgroupRestriction_inducedMap h d) τ

/-- The sheaf trace is exactly the existing full rational trace. -/
theorem subgroupRestrictionCoefficientTrace_eq (τ : Representation R G M) :
    subgroupRestrictionCoefficientTrace h d τ =
      SheafVariation.coefficientTrace (subgroupRestriction h d)
        (isCoveringMap_subgroupRestriction_inducedMap h d) τ := rfl

/-- Evaluation retains the original inverse-open point map and its entire fiber. -/
@[simp]
theorem subgroupRestrictionCoefficientTrace_apply (τ : Representation R G M)
    (A : ActionOpens G ((inclusion U).obj d).InducedSpectrum)
    (s : LocallyConstant ((SheafVariation.preimage (subgroupRestriction h d)).obj A).openSet M)
    (y : A.openSet) :
    LocallyConstant.toFun
        (((subgroupRestrictionCoefficientTrace h d τ).hom.app (op A)).hom s) y =
      fiberSum (DirectImage.pointMap (subgroupRestriction h d).inducedMap
        (subgroupRestriction h d).inducedMap_smul A) s y := rfl

/-- The proved relative index is the degree on every original open section. -/
theorem subgroupRestrictionCoefficientTrace_pullback_apply (τ : Representation R G M)
    (A : ActionOpens G ((inclusion U).obj d).InducedSpectrum)
    (s : LocallyConstant A.openSet M) (y : A.openSet) :
    LocallyConstant.toFun
        (((SheafVariation.coefficientMap (subgroupRestriction h d) τ ≫
          subgroupRestrictionCoefficientTrace h d τ).hom.app (op A)).hom s) y =
      V.toSubgroup.relIndex U.toSubgroup • s y := by
  rw [subgroupRestrictionCoefficientTrace_eq,
    SheafVariation.coefficientTrace_pullback_apply,
    card_subgroupRestriction_inducedMap_fiber]

/-- Full coefficient naturality requires no supplied covering or finite-fiber witness. -/
def subgroupRestrictionCoefficientTraceNatTrans :
    SheafVariation.coefficientFunctor
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) R ⋙
      SheafVariation.directImage (ModuleCat.{max (max u v) w} R)
        (subgroupRestriction h d) ⟶
      SheafVariation.coefficientFunctor ((inclusion U).obj d) R :=
  SheafVariation.coefficientTraceNatTrans (subgroupRestriction h d)
    (isCoveringMap_subgroupRestriction_inducedMap h d)

@[simp]
theorem subgroupRestrictionCoefficientTraceNatTrans_app (N : Rep.{w} R G) :
    (subgroupRestrictionCoefficientTraceNatTrans (R := R) h d).app N =
      subgroupRestrictionCoefficientTrace h d N.ρ := rfl

/-- Every original coefficient intertwiner commutes with this same trace. -/
@[reassoc]
theorem subgroupRestrictionCoefficientTrace_naturality {N N' : Rep.{w} R G}
    (a : N ⟶ N') :
    (SheafVariation.directImage (ModuleCat.{max (max u v) w} R)
        (subgroupRestriction h d)).map
        ((SheafVariation.coefficientFunctor
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) R).map a) ≫
        subgroupRestrictionCoefficientTrace h d N'.ρ =
      subgroupRestrictionCoefficientTrace h d N.ρ ≫
        (SheafVariation.coefficientFunctor ((inclusion U).obj d) R).map a :=
  (subgroupRestrictionCoefficientTraceNatTrans h d).naturality a

end Sheaf

section CompactSupport

open CompactSections

/-- Pull back all compactly supported smooth coefficients using the proved properness. -/
def subgroupRestrictionCompactSupportPullback (M : SmoothRep.{r, v, w} R G) :
    smoothRepresentation ((inclusion U).obj d) M ⟶
      smoothRepresentation
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) M :=
  Hom.compactSupportPullback (subgroupRestriction h d)
    (isProperMap_subgroupRestriction_inducedMap h d) M

/-- Trace all compactly supported smooth coefficients using the proved covering. -/
def subgroupRestrictionCompactSupportTrace (M : SmoothRep.{r, v, w} R G) :
    smoothRepresentation
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) M ⟶
      smoothRepresentation ((inclusion U).obj d) M :=
  Hom.compactSupportTrace (subgroupRestriction h d)
    (isCoveringMap_subgroupRestriction_inducedMap h d) M

@[simp]
theorem subgroupRestrictionCompactSupportPullback_apply
    (M : SmoothRep.{r, v, w} R G)
    (s : Functions (R := R) (V := M) ((inclusion U).obj d))
    (z : ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).InducedSpectrum) :
    (SmoothRep.hom (subgroupRestrictionCompactSupportPullback h d M) s).val z =
      s.val ((subgroupRestriction h d).inducedMap z) := rfl

@[simp]
theorem subgroupRestrictionCompactSupportTrace_apply (M : SmoothRep.{r, v, w} R G)
    (s : Functions (R := R) (V := M)
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)))
    (y : ((inclusion U).obj d).InducedSpectrum) :
    (SmoothRep.hom (subgroupRestrictionCompactSupportTrace h d M) s).val y =
      fiberSum (subgroupRestriction h d).inducedMap s.val y := rfl

/-- The entire original compact trace can be indexed by all actual relative cosets. -/
theorem subgroupRestrictionCompactSupportTrace_apply_sum
    (M : SmoothRep.{r, v, w} R G)
    (s : Functions (R := R) (V := M)
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)))
    (y : ((inclusion U).obj d).InducedSpectrum)
    [Fintype (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)] :
    (SmoothRep.hom (subgroupRestrictionCompactSupportTrace h d M) s).val y =
      ∑ c : U ⧸ V.toSubgroup.subgroupOf U.toSubgroup,
        s.val (subgroupRestrictionFiberHomeomorph h d y c).val :=
  fiberSum_eq_sum (subgroupRestriction h d).inducedMap s.val y
    (subgroupRestrictionFiberHomeomorph h d y).toEquiv

/-- The original compact pullback followed by trace multiplies by relative index. -/
theorem subgroupRestrictionCompactSupportTrace_pullback_apply
    (M : SmoothRep.{r, v, w} R G)
    (s : Functions (R := R) (V := M) ((inclusion U).obj d))
    (y : ((inclusion U).obj d).InducedSpectrum) :
    (SmoothRep.hom (subgroupRestrictionCompactSupportPullback h d M ≫
      subgroupRestrictionCompactSupportTrace h d M) s).val y =
        V.toSubgroup.relIndex U.toSubgroup • s.val y := by
  change fiberSum (subgroupRestriction h d).inducedMap
    (s.val ∘ (subgroupRestriction h d).inducedMap) y = _
  rw [fiberSum_comap, card_subgroupRestriction_inducedMap_fiber]

/-- Proper pullback remains natural on the entire original smooth coefficient category. -/
def subgroupRestrictionCompactSupportPullbackNatTrans :
    (coefficientFunctor ((inclusion U).obj d) :
      SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G) ⟶
        coefficientFunctor
          ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) :=
  Hom.compactSupportPullbackNatTrans (subgroupRestriction h d)
    (isProperMap_subgroupRestriction_inducedMap h d)

/-- Finite covering trace remains natural on every original smooth coefficient. -/
def subgroupRestrictionCompactSupportTraceNatTrans :
    (coefficientFunctor
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) :
      SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G) ⟶
        coefficientFunctor ((inclusion U).obj d) :=
  Hom.compactSupportTraceNatTrans (subgroupRestriction h d)
    (isCoveringMap_subgroupRestriction_inducedMap h d)

@[simp]
theorem subgroupRestrictionCompactSupportPullbackNatTrans_app
    (M : SmoothRep.{r, v, w} R G) :
    (subgroupRestrictionCompactSupportPullbackNatTrans (R := R) h d).app M =
      subgroupRestrictionCompactSupportPullback h d M := rfl

@[simp]
theorem subgroupRestrictionCompactSupportTraceNatTrans_app
    (M : SmoothRep.{r, v, w} R G) :
    (subgroupRestrictionCompactSupportTraceNatTrans (R := R) h d).app M =
      subgroupRestrictionCompactSupportTrace h d M := rfl

end CompactSupport

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
