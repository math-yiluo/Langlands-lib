import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousLocus
import Langlands.Topology.GroupAction.CompactLocallyConstantStabilizer

/-! # Locally constant functions on actual compact represented domain loci -/

noncomputable section

universe u v w t

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H) {A : Type w}

/-- The open subgroup fixing an actual locally constant function on the
represented locus, constructed using compactness and the original joint action. -/
def invariantLocusFunctionStabilizer
    (f : LocallyConstant d.obj.locus A) : OpenSubgroup H := by
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  letI : MulAction H d.obj.locus :=
    inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
      (ρ.invariantLocusAction H d)))
  letI : ContinuousSMul H d.obj.locus := ρ.invariantLocusAction_isContinuous H d
  exact CompactAction.openStabilizer H f

@[simp]
theorem mem_invariantLocusFunctionStabilizer
    (f : LocallyConstant d.obj.locus A) (g : H) :
    g ∈ ρ.invariantLocusFunctionStabilizer H d f ↔
      ∀ x, f (ρ.invariantLocusOperator H d g x) = f x := Iff.rfl

/-- Pull the function back along the exact original structural quotient. -/
def invariantLocusFunctionPullback
    (f : LocallyConstant d.obj.locus A) :
    LocallyConstant (BanachSpectrum d.obj.algebra) A :=
  LocallyConstant.comap d.obj.spectrumToLocus f

@[simp]
theorem invariantLocusFunctionPullback_apply
    (f : LocallyConstant d.obj.locus A) (x : BanachSpectrum d.obj.algebra) :
    ρ.invariantLocusFunctionPullback H d f x = f (d.obj.spectrumToLocus x) := rfl

/-- Openness also follows directly for functions on the actual representing
spectrum, using its proved local spectral joint continuity. -/
def invariantSpectrumFunctionStabilizer
    (f : LocallyConstant (BanachSpectrum d.obj.algebra) A) : OpenSubgroup H := by
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  letI : MulAction H (BanachSpectrum d.obj.algebra) :=
    inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
      ((ρ.invariantSpectrumActionFunctor H).obj d)))
  letI : ContinuousSMul H (BanachSpectrum d.obj.algebra) :=
    ρ.invariantSpectrumAction_isContinuous H d
  exact CompactAction.openStabilizer H f

@[simp]
theorem mem_invariantSpectrumFunctionStabilizer
    (f : LocallyConstant (BanachSpectrum d.obj.algebra) A) (g : H) :
    g ∈ ρ.invariantSpectrumFunctionStabilizer H d f ↔
      ∀ x, f ((ρ.invariantSectionAction H d g) • x) = f x := Iff.rfl

/-- The original surjective quotient detects the full function stabilizer.
No injectivity of the spectrum-to-locus map is used. -/
theorem invariantLocusFunctionPullback_stabilizer
    (f : LocallyConstant d.obj.locus A) :
    ρ.invariantSpectrumFunctionStabilizer H d
        (ρ.invariantLocusFunctionPullback H d f) =
      ρ.invariantLocusFunctionStabilizer H d f := by
  apply OpenSubgroup.ext
  intro g
  rw [mem_invariantSpectrumFunctionStabilizer, mem_invariantLocusFunctionStabilizer]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := d.obj.spectrumToLocus_surjective y
    have heq : d.obj.spectrumToLocus ((ρ.invariantSectionAction H d g) • x) =
        ρ.invariantLocusOperator H d g (d.obj.spectrumToLocus x) :=
      congrArg (fun k => k x) ((ρ.invariantSpectrumToLocus H d).comm g)
    exact (congrArg f heq).symm.trans (h x)
  · intro h x
    have heq : d.obj.spectrumToLocus ((ρ.invariantSectionAction H d g) • x) =
        ρ.invariantLocusOperator H d g (d.obj.spectrumToLocus x) :=
      congrArg (fun k => k x) ((ρ.invariantSpectrumToLocus H d).comm g)
    exact (congrArg f heq).trans (h (d.obj.spectrumToLocus x))

/-- A finite family on the original represented locus has one actual common
open subgroup of its preserving group. -/
def invariantLocusFiniteFunctionStabilizer {ι : Type t} [Finite ι]
    (f : ι → LocallyConstant d.obj.locus A) : OpenSubgroup H :=
  OpenSubgroup.iInfOfFinite (fun i => ρ.invariantLocusFunctionStabilizer H d (f i))

@[simp]
theorem mem_invariantLocusFiniteFunctionStabilizer {ι : Type t} [Finite ι]
    (f : ι → LocallyConstant d.obj.locus A) (g : H) :
    g ∈ ρ.invariantLocusFiniteFunctionStabilizer H d f ↔
      ∀ i x, f i (ρ.invariantLocusOperator H d g x) = f i x := by
  change (g ∈ (⨅ i, (ρ.invariantLocusFunctionStabilizer H d (f i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf]
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
