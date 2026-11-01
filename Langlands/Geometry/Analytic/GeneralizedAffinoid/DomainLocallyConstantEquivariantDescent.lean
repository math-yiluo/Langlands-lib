import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantDescent
import Langlands.Topology.GroupAction.LocallyConstantQuotientAction

/-! # Equivariant locally constant descent through original domain spectra -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology CompactAction

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H) (A : Type w)

local instance : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

local instance : MulAction H d.obj.locus :=
  inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
    (ρ.invariantLocusAction H d)))

local instance : ContinuousSMul H d.obj.locus :=
  ρ.invariantLocusAction_isContinuous H d

local instance : MulAction H (BanachSpectrum d.obj.algebra) :=
  inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
    ((ρ.invariantSpectrumActionFunctor H).obj d)))

local instance : ContinuousSMul H (BanachSpectrum d.obj.algebra) :=
  ρ.invariantSpectrumAction_isContinuous H d

/-- The unchanged original structural quotient is equivariant for the actual actions. -/
theorem invariantStructuralQuotient_equivariant (g : H)
    (x : BanachSpectrum d.obj.algebra) :
    d.obj.spectrumToLocus (g • x) = g • d.obj.spectrumToLocus x :=
  congrArg (fun k => k x) ((ρ.invariantSpectrumToLocus H d).comm g)

/-- The entire subtype satisfying the original structural quotient fiber equations,
with its inherited discrete jointly continuous action. -/
def invariantSpectrumFiberLocallyConstantAction : ContAction TopCat.{max u w} H :=
  DiscreteLocallyConstant.compatibleContinuousAction (A := A) H d.obj.spectrumToLocus
    (ρ.invariantStructuralQuotient_equivariant H d)

/-- The original subtype inclusion is a continuous equivariant map to all spectrum functions. -/
def invariantSpectrumFiberLocallyConstantInclusion :
    ρ.invariantSpectrumFiberLocallyConstantAction H d A ⟶
      ρ.invariantSpectrumLocallyConstantAction H d A :=
  DiscreteLocallyConstant.compatibleInclusion (A := A) H d.obj.spectrumToLocus
    (ρ.invariantStructuralQuotient_equivariant H d)

/-- The original structural quotient constructs continuous equivariant descent,
with no injectivity premise or supplied descended function. -/
def invariantLocallyConstantDescentIso :
    ρ.invariantLocusLocallyConstantAction H d A ≅
      ρ.invariantSpectrumFiberLocallyConstantAction H d A :=
  DiscreteLocallyConstant.compatibleDescentIso (A := A) H d.obj.spectrumToLocus
    (ρ.invariantStructuralQuotient_equivariant H d) d.obj.spectrumToLocus_isQuotientMap

@[simp]
theorem invariantLocallyConstantDescentIso_hom_apply
    (f : DiscreteLocallyConstant d.obj.locus A) (x : BanachSpectrum d.obj.algebra) :
    ((ρ.invariantLocallyConstantDescentIso H d A).hom.hom.hom f).val x =
      f (d.obj.spectrumToLocus x) := rfl

@[simp]
theorem invariantLocallyConstantDescentIso_inv_apply
    (f : DiscreteLocallyConstant.FiberCompatible d.obj.spectrumToLocus A)
    (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      ((ρ.invariantLocallyConstantDescentIso H d A).inv.hom.hom f))
        (d.obj.spectrumToLocus x) = f.val x :=
  DiscreteLocallyConstant.compatibleDescend_apply d.obj.spectrumToLocus
    d.obj.spectrumToLocus_isQuotientMap f x

/-- Forgetting fiber compatibility recovers exactly the earlier structural pullback. -/
theorem invariantLocallyConstantDescentIso_hom_inclusion :
    (ρ.invariantLocallyConstantDescentIso H d A).hom ≫
        ρ.invariantSpectrumFiberLocallyConstantInclusion H d A =
      ρ.invariantLocallyConstantActionPullback H d A := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro f
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
