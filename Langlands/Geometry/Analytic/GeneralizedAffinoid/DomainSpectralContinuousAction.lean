import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralLocalContinuityProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantActions

/-! # Continuous spectra of invariant represented affinoid domains
-/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- The actual inverse-pullback action of the open rational-locus stabilizer. -/
def spectrumAction (d : Domain K P) :
    Action TopCat.{u} (ρ.locusOpenSubgroup d) where
  V := TopCat.of (BanachSpectrum d.algebra)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        (BanachSpectrum.comapContinuous (ρ.sectionAction d g).inv.toBoundedRingHom)
      map_one' := by
        apply TopCat.ext
        intro x
        change (ρ.sectionAction d 1) • x = x
        simp
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        change (ρ.sectionAction d (g * h)) • x =
          (ρ.sectionAction d g) • ((ρ.sectionAction d h) • x)
        rw [map_mul, mul_smul] }

/-- The actual local continuous spectrum action from the proved local theorem. -/
def spectrum (d : Domain K P) :
    ContAction TopCat.{u} (ρ.locusOpenSubgroup d) :=
  ⟨ρ.spectrumAction d, (Action.isContinuous_def _).mpr
    ((domainSpectralLocalContinuity K P G ρ d).2.2)⟩

@[simp]
theorem spectrum_apply (d : Domain K P) (g : ρ.locusOpenSubgroup d)
    (x : BanachSpectrum d.algebra) (b : d.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.spectrum d).obj.ρ g) x) b =
        x ((ρ.sectionAction d g).inv.toAlgHom b) :=
  rfl

/-- The existing actual spectrum diagram satisfies joint continuity after
restriction along the constructed continuous stabilizer inclusion. -/
theorem invariantSpectrumAction_isContinuous (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    ((ρ.invariantSpectrumActionFunctor H).obj d).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  change Continuous (fun p : H × BanachSpectrum d.obj.algebra =>
    (ρ.invariantSectionAction H d p.1) • p.2)
  have hc : Continuous
      (fun p : ρ.locusOpenSubgroup d.obj × BanachSpectrum d.obj.algebra =>
        (ρ.sectionAction d.obj p.1) • p.2) :=
    (domainSpectralLocalContinuity K P G ρ d.obj).2.2
  have hi : Continuous (fun p : H × BanachSpectrum d.obj.algebra =>
      (ρ.invariantStabilizerInclusion H d p.1, p.2)) :=
    ((ρ.invariantStabilizerInclusion H d).continuous.comp continuous_fst).prodMk
      continuous_snd
  have hcont := hc.comp hi
  change Continuous (fun p : H × BanachSpectrum d.obj.algebra =>
    (ρ.sectionAction d.obj (ρ.invariantStabilizerInclusion H d p.1)) • p.2)
  exact hcont

/-- Lift the previously constructed diagram through the full subcategory of
continuous actions, retaining every bounded restriction literally. -/
def invariantSpectrumFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ ContAction TopCat.{u} H :=
  (Action.isContinuous TopCat.{u} H).lift
    (ρ.invariantSpectrumActionFunctor H)
    (ρ.invariantSpectrumAction_isContinuous H)

/-- The continuous lift has exactly the previous equivariant diagram. -/
@[simp]
theorem invariantSpectrumFunctor_toAction (H : OpenSubgroup G) :
    ρ.invariantSpectrumFunctor H ⋙ (Action.isContinuous TopCat.{u} H).ι =
      ρ.invariantSpectrumActionFunctor H :=
  rfl

@[simp]
theorem invariantSpectrumFunctor_obj_apply (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (g : H) (x : BanachSpectrum d.obj.algebra)
    (b : d.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (((ρ.invariantSpectrumFunctor H).obj d).obj.ρ g) x) b =
        x ((ρ.invariantSectionAction H d g).inv.toAlgHom b) :=
  rfl

@[simp]
theorem invariantSpectrumFunctor_map_apply (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e)
    (x : BanachSpectrum d.obj.algebra) (b : e.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.invariantSpectrumFunctor H).map f).hom.hom x) b =
        x (f.hom.restriction b) :=
  rfl

/-- Forgetting continuity and the action recovers the actual represented-domain
spectrum diagram, including all of its bounded restrictions. -/
@[simp]
theorem invariantSpectrumFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantSpectrumFunctor H ⋙ forget₂ _ TopCat.{u} =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.toTopologicalSpace K P :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
