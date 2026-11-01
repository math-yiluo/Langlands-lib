import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Langlands.Topology.LocallyConstant.QuotientDescent

/-! # Locally constant descent from actual representing spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K} {A : Type v}

/-- The actual structural quotient gives descent precisely for functions
constant on its fibers, without identifying the spectrum with the locus. -/
def spectrumLocallyConstantEquiv (d : Domain K P) :
    LocallyConstant d.locus A ≃
      {f : LocallyConstant (BanachSpectrum d.algebra) A //
        Function.FactorsThrough f d.spectrumToLocus} :=
  LocallyConstantQuotient.descentEquiv d.spectrumToLocus
    d.spectrumToLocus_isQuotientMap

namespace FiniteCover

variable {d : Domain K P} (c : FiniteCover d)

/-- The direct spectrum-input compatibility equations, also within each spectrum. -/
def SpectrumLocallyConstantCompatible
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A) : Prop :=
  ∀ (i j : Fin c.size) (x : BanachSpectrum (c.obj i).algebra)
    (y : BanachSpectrum (c.obj j).algebra),
    c.componentMap i x = c.componentMap j y → f i x = f j y

/-- Assemble locally constant functions on the unchanged disjoint union of spectra. -/
def spectrumLocallyConstantFamily
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A) :
    LocallyConstant (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) A where
  toFun x := f x.1 x.2
  isLocallyConstant s := isOpen_sigma_iff.mpr fun i => (f i).isLocallyConstant s

theorem spectrumLocallyConstantFamily_factorsThrough
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A)
    (hf : c.SpectrumLocallyConstantCompatible f) :
    Function.FactorsThrough (c.spectrumLocallyConstantFamily f) c.totalMap := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  exact hf i j x y h

/-- Restriction directly to each actual component spectrum. -/
def spectrumLocallyConstantRestrict (f : LocallyConstant d.locus A) (i : Fin c.size) :
    LocallyConstant (BanachSpectrum (c.obj i).algebra) A :=
  LocallyConstant.comap (c.componentMap i) f

theorem spectrumLocallyConstantCompatible_restrict (f : LocallyConstant d.locus A) :
    c.SpectrumLocallyConstantCompatible (c.spectrumLocallyConstantRestrict f) :=
  fun _ _ _ _ h => congrArg f h

/-- Construct the downstairs function from direct spectrum data and the complete
fiber equations, using the original finite-cover quotient topology. -/
def spectrumLocallyConstantGlue
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A)
    (hf : c.SpectrumLocallyConstantCompatible f) : LocallyConstant d.locus A :=
  LocallyConstantQuotient.descend c.totalMap c.totalMap_isQuotientMap
    (c.spectrumLocallyConstantFamily f)
    (c.spectrumLocallyConstantFamily_factorsThrough f hf)

@[simp]
theorem spectrumLocallyConstantGlue_apply
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A)
    (hf : c.SpectrumLocallyConstantCompatible f) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    c.spectrumLocallyConstantGlue f hf (c.componentMap i x) = f i x :=
  LocallyConstantQuotient.descend_apply c.totalMap c.totalMap_isQuotientMap
    (c.spectrumLocallyConstantFamily f)
    (c.spectrumLocallyConstantFamily_factorsThrough f hf) ⟨i, x⟩

@[simp]
theorem spectrumLocallyConstantRestrict_glue
    (f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A)
    (hf : c.SpectrumLocallyConstantCompatible f) :
    c.spectrumLocallyConstantRestrict (c.spectrumLocallyConstantGlue f hf) = f := by
  funext i
  ext x
  exact c.spectrumLocallyConstantGlue_apply f hf i x

@[simp]
theorem spectrumLocallyConstantGlue_restrict (f : LocallyConstant d.locus A) :
    c.spectrumLocallyConstantGlue (c.spectrumLocallyConstantRestrict f)
      (c.spectrumLocallyConstantCompatible_restrict f) = f := by
  ext y
  obtain ⟨⟨i, x⟩, rfl⟩ := c.totalMap_surjective y
  exact c.spectrumLocallyConstantGlue_apply _ _ i x

/-- Locally constant functions on the target are exactly fiber-compatible
locally constant functions on the actual component spectra. -/
def spectrumLocallyConstantEquiv :
    LocallyConstant d.locus A ≃
      {f : ∀ i : Fin c.size, LocallyConstant (BanachSpectrum (c.obj i).algebra) A //
        c.SpectrumLocallyConstantCompatible f} where
  toFun f := ⟨c.spectrumLocallyConstantRestrict f,
    c.spectrumLocallyConstantCompatible_restrict f⟩
  invFun f := c.spectrumLocallyConstantGlue f.val f.property
  left_inv := c.spectrumLocallyConstantGlue_restrict
  right_inv f := Subtype.ext (c.spectrumLocallyConstantRestrict_glue f.val f.property)

end FiniteCover
end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
