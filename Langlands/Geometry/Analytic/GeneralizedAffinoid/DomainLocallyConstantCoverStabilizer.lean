import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantStabilizer
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFiniteInvariantCover

/-! # The exact open stabilizer of a function glued from actual spectra -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
  (c : Domain.FiniteCover d.obj) {A : Type w}

/-- The original component operator, with its unchanged spectrum carrier
explicit in its type. -/
def finiteCoverComponentSpectrumOperator
    (g : ρ.finiteFamilyOpenSubgroup H c.obj) (i : Fin c.size) :
    C(BanachSpectrum (c.obj i).algebra, BanachSpectrum (c.obj i).algebra) :=
  ((ρ.finiteCoverComponentAction H d c i).ρ g).hom

/-- The finite intersection of the full component-spectrum function stabilizers,
inside the original common subgroup preserving the cover. -/
def finiteCoverSpectrumFunctionStabilizer
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A) :
    OpenSubgroup (ρ.finiteFamilyOpenSubgroup H c.obj) :=
  OpenSubgroup.iInfOfFinite fun i =>
    ρ.invariantSpectrumFunctionStabilizer (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantFamily H c.obj i) (f i)

@[simp]
theorem mem_finiteCoverSpectrumFunctionStabilizer
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A)
    (g : ρ.finiteFamilyOpenSubgroup H c.obj) :
    g ∈ ρ.finiteCoverSpectrumFunctionStabilizer H d c f ↔
      ∀ i x, f i (ρ.finiteCoverComponentSpectrumOperator H d c g i x) = f i x := by
  change (g ∈ (⨅ i, (ρ.invariantSpectrumFunctionStabilizer
    (ρ.finiteFamilyOpenSubgroup H c.obj)
    (ρ.finiteInvariantFamily H c.obj i) (f i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf]
  rfl

/-- The original component quotient intertwines the original spectrum action
and the restricted target-locus action. -/
theorem finiteCoverComponent_smul
    (g : ρ.finiteFamilyOpenSubgroup H c.obj) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    c.componentMap i
        (ρ.finiteCoverComponentSpectrumOperator H d c g i x) =
      ρ.invariantLocusOperator (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) g (c.componentMap i x) :=
  ConcreteCategory.congr_hom ((ρ.finiteCoverComponent H d c i).comm g) x

/-- Descent retains the entire stabilizer: the subgroup fixing every supplied
spectrum function is exactly the subgroup fixing the constructed locus function. -/
theorem finiteCoverSpectrumFunctionStabilizer_glue
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A)
    (hf : c.SpectrumLocallyConstantCompatible f) :
    ρ.finiteCoverSpectrumFunctionStabilizer H d c f =
      ρ.invariantLocusFunctionStabilizer (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj)
        (c.spectrumLocallyConstantGlue f hf) := by
  apply OpenSubgroup.ext
  intro g
  rw [mem_finiteCoverSpectrumFunctionStabilizer]
  change (∀ i x,
      f i (ρ.finiteCoverComponentSpectrumOperator H d c g i x) = f i x) ↔
    ∀ y : d.obj.locus, c.spectrumLocallyConstantGlue f hf
      (ρ.invariantLocusOperator (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) g y) =
      c.spectrumLocallyConstantGlue f hf y
  constructor
  · intro h y
    obtain ⟨⟨i, x⟩, rfl⟩ := c.totalMap_surjective y
    change c.spectrumLocallyConstantGlue f hf
      (ρ.invariantLocusOperator (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) g (c.componentMap i x)) =
      c.spectrumLocallyConstantGlue f hf (c.componentMap i x)
    rw [← ρ.finiteCoverComponent_smul H d c g i x,
      c.spectrumLocallyConstantGlue_apply, c.spectrumLocallyConstantGlue_apply]
    exact h i x
  · intro h i x
    have heq := congrArg (c.spectrumLocallyConstantGlue f hf)
      (ρ.finiteCoverComponent_smul H d c g i x)
    rw [c.spectrumLocallyConstantGlue_apply] at heq
    calc
      f i (ρ.finiteCoverComponentSpectrumOperator H d c g i x) =
          c.spectrumLocallyConstantGlue f hf
            (ρ.invariantLocusOperator (ρ.finiteFamilyOpenSubgroup H c.obj)
              (ρ.finiteInvariantTarget H d c.obj) g (c.componentMap i x)) := heq
      _ = c.spectrumLocallyConstantGlue f hf (c.componentMap i x) := h _
      _ = f i x := c.spectrumLocallyConstantGlue_apply f hf i x

/-- Restriction to the full covering spectra detects the full locus stabilizer. -/
theorem finiteCoverSpectrumFunctionStabilizer_restrict
    (f : LocallyConstant d.obj.locus A) :
    ρ.finiteCoverSpectrumFunctionStabilizer H d c
        (c.spectrumLocallyConstantRestrict f) =
      ρ.invariantLocusFunctionStabilizer (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) f := by
  rw [ρ.finiteCoverSpectrumFunctionStabilizer_glue H d c
    (c.spectrumLocallyConstantRestrict f)
    (c.spectrumLocallyConstantCompatible_restrict f),
    c.spectrumLocallyConstantGlue_restrict]

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
