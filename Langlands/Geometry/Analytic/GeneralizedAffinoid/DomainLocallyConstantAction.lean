import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantStabilizer
import Langlands.Topology.GroupAction.CompactLocallyConstantAction

/-! # Discrete continuous function actions on actual represented domains -/

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

/-- Inverse precomposition on the discrete locally constant functions of the
actual invariant compact represented locus, with the original topology on H. -/
def invariantLocusLocallyConstantAction : ContAction TopCat.{max u w} H := by
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  letI : MulAction H d.obj.locus :=
    inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
      (ρ.invariantLocusAction H d)))
  letI : ContinuousSMul H d.obj.locus := ρ.invariantLocusAction_isContinuous H d
  exact DiscreteLocallyConstant.continuousAction (X := d.obj.locus) (A := A) H

@[simp]
theorem invariantLocusLocallyConstantAction_apply (g : H)
    (f : DiscreteLocallyConstant d.obj.locus A) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant
      (ConcreteCategory.hom ((ρ.invariantLocusLocallyConstantAction H d A).obj.ρ g) f)) x =
      f (ρ.invariantLocusOperator H d g⁻¹ x) := rfl

/-- The original representing spectrum, including all structural fibers, gives
its own discrete continuous locally constant function action. -/
def invariantSpectrumLocallyConstantAction : ContAction TopCat.{max u w} H := by
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  letI : MulAction H (BanachSpectrum d.obj.algebra) :=
    inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
      ((ρ.invariantSpectrumActionFunctor H).obj d)))
  letI : ContinuousSMul H (BanachSpectrum d.obj.algebra) :=
    ρ.invariantSpectrumAction_isContinuous H d
  exact DiscreteLocallyConstant.continuousAction
    (X := BanachSpectrum d.obj.algebra) (A := A) H

@[simp]
theorem invariantSpectrumLocallyConstantAction_apply (g : H)
    (f : DiscreteLocallyConstant (BanachSpectrum d.obj.algebra) A)
    (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      (ConcreteCategory.hom ((ρ.invariantSpectrumLocallyConstantAction H d A).obj.ρ g) f)) x =
      f ((ρ.invariantSectionAction H d g⁻¹) • x) := rfl

/-- The original structural quotient induces an equivariant continuous pullback
between the constructed discrete continuous function actions. -/
def invariantLocallyConstantActionPullback :
    ρ.invariantLocusLocallyConstantAction H d A ⟶
      ρ.invariantSpectrumLocallyConstantAction H d A :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨DiscreteLocallyConstant.pullback d.obj.spectrumToLocus,
          continuous_of_discreteTopology⟩
      comm := fun g => by
        apply TopCat.ext
        intro f
        let f' : DiscreteLocallyConstant d.obj.locus A := f
        apply DiscreteLocallyConstant.ext
        intro x
        change f' (ρ.invariantLocusOperator H d g⁻¹ (d.obj.spectrumToLocus x)) =
          f' (d.obj.spectrumToLocus ((ρ.invariantSectionAction H d g⁻¹) • x))
        have heq : d.obj.spectrumToLocus ((ρ.invariantSectionAction H d g⁻¹) • x) =
            ρ.invariantLocusOperator H d g⁻¹ (d.obj.spectrumToLocus x) :=
          congrArg (fun k => k x) ((ρ.invariantSpectrumToLocus H d).comm g⁻¹)
        exact congrArg f' heq.symm }

@[simp]
theorem invariantLocallyConstantActionPullback_apply
    (f : DiscreteLocallyConstant d.obj.locus A) (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      ((ρ.invariantLocallyConstantActionPullback H d A).hom.hom f)) x =
      f (d.obj.spectrumToLocus x) := rfl

/-- Injectivity uses the proved surjectivity of the unchanged structural quotient. -/
theorem invariantLocallyConstantActionPullback_injective :
    Function.Injective (ρ.invariantLocallyConstantActionPullback H d A).hom.hom :=
  DiscreteLocallyConstant.pullback_injective d.obj.spectrumToLocus
    d.obj.spectrumToLocus_surjective

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
