import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantActions
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Equivariant quotient presentations of actual represented loci -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- The ambient inverse-pullback operator restricts to each invariant represented
locus, continuously for each fixed element of the common subgroup. -/
def invariantLocusOperator (H : OpenSubgroup G) (d : ρ.InvariantDomain H) (g : H) :
    C(d.obj.locus, d.obj.locus) where
  toFun x := ⟨ρ.toMonoidHom (g : G) • (x : BanachSpectrum P),
    smul_mem_locus d.obj
      (ρ.stabilizerHom d.obj (ρ.invariantStabilizerInclusion H d g)) x.property⟩
  continuous_toFun :=
    ((BanachSpectrum.comapContinuous
      (ρ.toMonoidHom (g : G)).inv.toBoundedRingHom).continuous.comp
        continuous_subtype_val).subtype_mk _

@[simp]
theorem invariantLocusOperator_coe (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    (g : H) (x : d.obj.locus) :
    (ρ.invariantLocusOperator H d g x : BanachSpectrum P) =
      ρ.toMonoidHom (g : G) • (x : BanachSpectrum P) :=
  rfl

/-- The actual closed represented subspace, with its restricted ambient action.
No joint continuity in the group parameter is used. -/
def invariantLocusAction (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    Action TopCat.{u} H where
  V := TopCat.of d.obj.locus
  ρ :=
    { toFun := fun g => TopCat.ofHom (ρ.invariantLocusOperator H d g)
      map_one' := by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        change ρ.toMonoidHom 1 • (x : BanachSpectrum P) = (x : BanachSpectrum P)
        rw [map_one, one_smul]
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        apply Subtype.ext
        change ρ.toMonoidHom ((g : G) * (h : G)) • (x : BanachSpectrum P) =
          ρ.toMonoidHom (g : G) • (ρ.toMonoidHom (h : G) • (x : BanachSpectrum P))
        rw [map_mul, mul_smul] }

/-- Actual bounded restrictions induce equivariant inclusions of represented
loci. The locus maps retain their original underlying spectrum points. -/
def invariantLocusActionFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ Action TopCat.{u} H where
  obj d := ρ.invariantLocusAction H d
  map f :=
    { hom := TopCat.ofHom f.hom.locusMap
      comm := fun _ => by
        apply TopCat.ext
        intro x
        rfl }
  map_id _ := by
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    rfl
  map_comp _ _ := by
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    rfl

@[simp]
theorem invariantLocusActionFunctor_map_apply (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) (x : d.obj.locus) :
    ((ρ.invariantLocusActionFunctor H).map f).hom x = f.hom.locusMap x :=
  rfl

/-- Forgetting the action recovers the exact represented-locus diagram. -/
@[simp]
theorem invariantLocusActionFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantLocusActionFunctor H ⋙ Action.forget TopCat.{u} H =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.locusFunctor K P :=
  rfl

/-- The original structural spectrum quotient is equivariant for the constructed
section action and the restricted ambient locus action. -/
def invariantSpectrumToLocus (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    (ρ.invariantSpectrumActionFunctor H).obj d ⟶
      (ρ.invariantLocusActionFunctor H).obj d where
  hom := TopCat.ofHom d.obj.spectrumToLocus
  comm g := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    exact ρ.spectrumMap_smul d.obj (ρ.invariantStabilizerInclusion H d g) x

@[simp]
theorem invariantSpectrumToLocus_apply (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    (x : BanachSpectrum d.obj.algebra) :
    (ρ.invariantSpectrumToLocus H d).hom x = d.obj.spectrumToLocus x :=
  rfl

/-- The equivariant structural map is surjective onto the actual closed locus. -/
theorem invariantSpectrumToLocus_surjective (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    Function.Surjective (ρ.invariantSpectrumToLocus H d).hom :=
  d.obj.spectrumToLocus_surjective

/-- Its underlying continuous map is closed. -/
theorem invariantSpectrumToLocus_isClosedMap (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    IsClosedMap (ρ.invariantSpectrumToLocus H d).hom :=
  d.obj.spectrumToLocus_isClosedMap

/-- Its underlying quotient topology is the actual subspace topology of the
represented locus. This makes no claim of injectivity on section spectra. -/
theorem invariantSpectrumToLocus_isQuotientMap (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    IsQuotientMap (ρ.invariantSpectrumToLocus H d).hom :=
  d.obj.spectrumToLocus_isQuotientMap

/-- Bounded restrictions give commuting equivariant spectrum-to-locus squares. -/
theorem invariantSpectrumToLocus_naturality (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    (ρ.invariantSpectrumActionFunctor H).map f ≫ ρ.invariantSpectrumToLocus H e =
      ρ.invariantSpectrumToLocus H d ≫ (ρ.invariantLocusActionFunctor H).map f := by
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  exact f.hom.spectrumToLocus_naturality x

/-- The exact structural spectrum quotients form an equivariant natural
transformation from section spectra to represented loci. -/
def invariantSpectrumToLocusNatTrans (H : OpenSubgroup G) :
    ρ.invariantSpectrumActionFunctor H ⟶ ρ.invariantLocusActionFunctor H where
  app d := ρ.invariantSpectrumToLocus H d
  naturality _ _ f := ρ.invariantSpectrumToLocus_naturality H f

/-- Forgetting equivariance retains the published structural quotient
transformation, including its components and naturality squares. -/
@[simp]
theorem invariantSpectrumToLocusNatTrans_forget (H : OpenSubgroup G) :
    Functor.whiskerRight (ρ.invariantSpectrumToLocusNatTrans H)
        (Action.forget TopCat.{u} H) =
      Functor.whiskerLeft (ρ.invariantDomainProperty H).ι (Domain.spectrumToLocusNat K P) :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
