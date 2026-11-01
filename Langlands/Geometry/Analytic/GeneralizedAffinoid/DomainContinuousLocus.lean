import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralContinuousAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralGlobalAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantLocus

/-! # Jointly continuous represented loci and their structural quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- The original ambient joint action restricts to each actual invariant locus
with its subspace topology. -/
theorem invariantLocusAction_isContinuous (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) : (ρ.invariantLocusAction H d).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  have hc : Continuous (fun p : H × d.obj.locus =>
      ρ.toMonoidHom (p.1 : G) • (p.2 : BanachSpectrum P)) :=
    ρ.continuous_globalSpectrumAction.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  exact hc.subtype_mk _

/-- Lift the full represented-locus diagram, preserving all its original
continuous inclusions. Joint continuity is proved, not supplied as input. -/
def invariantLocusFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ ContAction TopCat.{u} H :=
  (Action.isContinuous TopCat.{u} H).lift
    (ρ.invariantLocusActionFunctor H) (ρ.invariantLocusAction_isContinuous H)

@[simp]
theorem invariantLocusFunctor_toAction (H : OpenSubgroup G) :
    ρ.invariantLocusFunctor H ⋙ (Action.isContinuous TopCat.{u} H).ι =
      ρ.invariantLocusActionFunctor H := rfl

@[simp]
theorem invariantLocusFunctor_obj_coe (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (g : H) (x : d.obj.locus) :
    ((show d.obj.locus from
      ConcreteCategory.hom (((ρ.invariantLocusFunctor H).obj d).obj.ρ g) x) :
      BanachSpectrum P) = ρ.toMonoidHom (g : G) • (x : BanachSpectrum P) := rfl

@[simp]
theorem invariantLocusFunctor_map_apply (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) (x : d.obj.locus) :
    ((ρ.invariantLocusFunctor H).map f).hom.hom x = f.hom.locusMap x := rfl

@[simp]
theorem invariantLocusFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantLocusFunctor H ⋙ forget₂ _ TopCat.{u} =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.locusFunctor K P := rfl

/-- The exact structural quotient is now a morphism of jointly continuous
actions. Its underlying bounded pullback and locus point are unchanged. -/
def invariantSpectrumToLocusContinuous (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    (ρ.invariantSpectrumFunctor H).obj d ⟶ (ρ.invariantLocusFunctor H).obj d :=
  ObjectProperty.homMk (ρ.invariantSpectrumToLocus H d)

@[simp]
theorem invariantSpectrumToLocusContinuous_apply (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (x : BanachSpectrum d.obj.algebra) :
    (ρ.invariantSpectrumToLocusContinuous H d).hom.hom x = d.obj.spectrumToLocus x := rfl

/-- Surjectivity is onto the represented locus, without asserting injectivity. -/
theorem invariantSpectrumToLocusContinuous_surjective (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    Function.Surjective (ρ.invariantSpectrumToLocusContinuous H d).hom.hom :=
  d.obj.spectrumToLocus_surjective

theorem invariantSpectrumToLocusContinuous_isClosedMap (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    IsClosedMap (ρ.invariantSpectrumToLocusContinuous H d).hom.hom :=
  d.obj.spectrumToLocus_isClosedMap

theorem invariantSpectrumToLocusContinuous_isQuotientMap (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    IsQuotientMap (ρ.invariantSpectrumToLocusContinuous H d).hom.hom :=
  d.obj.spectrumToLocus_isQuotientMap

/-- All original bounded restrictions retain their structural quotient square. -/
theorem invariantSpectrumToLocusContinuous_naturality (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    (ρ.invariantSpectrumFunctor H).map f ≫ ρ.invariantSpectrumToLocusContinuous H e =
      ρ.invariantSpectrumToLocusContinuous H d ≫ (ρ.invariantLocusFunctor H).map f := by
  apply ObjectProperty.hom_ext _
  exact ρ.invariantSpectrumToLocus_naturality H f

/-- The actual structural quotients form a natural transformation between
the jointly continuous spectrum and locus diagrams. -/
def invariantSpectrumToLocusContinuousNatTrans (H : OpenSubgroup G) :
    ρ.invariantSpectrumFunctor H ⟶ ρ.invariantLocusFunctor H where
  app d := ρ.invariantSpectrumToLocusContinuous H d
  naturality _ _ f := ρ.invariantSpectrumToLocusContinuous_naturality H f

@[simp]
theorem invariantSpectrumToLocusContinuousNatTrans_toAction (H : OpenSubgroup G) :
    Functor.whiskerRight (ρ.invariantSpectrumToLocusContinuousNatTrans H)
        (Action.isContinuous TopCat.{u} H).ι =
      ρ.invariantSpectrumToLocusNatTrans H := rfl

/-- Forgetting both action structures recovers the original topological
quotient transformation on all invariant represented domains. -/
@[simp]
theorem invariantSpectrumToLocusContinuousNatTrans_forget (H : OpenSubgroup G) :
    Functor.whiskerRight (ρ.invariantSpectrumToLocusContinuousNatTrans H)
        (forget₂ _ TopCat.{u}) =
      Functor.whiskerLeft (ρ.invariantDomainProperty H).ι (Domain.spectrumToLocusNat K P) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
