import Langlands.Geometry.Analytic.ClopenPieceLocalization
import Langlands.Geometry.Analytic.EtaleMonomorphism
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.SmallAffinoidEtaleRealization
import Langlands.Geometry.Analytic.SmallAffinoidRingPushout
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Clopen affinoid domains in the localized category -/

noncomputable section

universe u v

namespace Langlands.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open SaturatedAtlasPresentation PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

variable {R : PresentedAffinoidAlgebra K} {C : Set (BanachSpectrum R)} (hC : IsClopen C)

theorem isFiniteBanach_clopenRationalChart :
    (clopenRationalChart C hC).baseMap.IsFiniteBanach := by
  obtain ⟨M, hM, hlift⟩ := exists_lift_clopenRationalChart C hC
  exact BoundedAlgHom.isFiniteBanach_of_lift _ hM hlift

theorem surjective_clopenRationalChart :
    Function.Surjective (clopenRationalChart C hC).baseMap := by
  obtain ⟨_, -, hlift⟩ := exists_lift_clopenRationalChart C hC
  intro z
  obtain ⟨a, ha, -⟩ := hlift z
  exact ⟨a, ha⟩

theorem algebraicallyFiniteEtale_clopenRationalChart :
    (clopenRationalChart C hC).baseMap.AlgebraicallyFiniteEtale := by
  let f := (clopenRationalChart C hC).baseMap
  have hfin := (isFiniteBanach_clopenRationalChart hC).finite
  have hsurj := surjective_clopenRationalChart hC
  let : Algebra R (clopenRationalChart C hC).algebra := f.toAlgHom.toRingHom.toAlgebra
  exact (BoundedAlgHom.algebraicallyFiniteEtale_iff f).mpr
    ⟨hfin, flat_clopenRationalChart C hC, RingHom.FormallyUnramified.of_surjective hsurj,
      Algebra.FinitePresentation.of_finiteType.mp hfin.finiteType⟩

theorem small_clopenRationalChart [Small.{v} (BanachSpectrum R)] :
    Small.{v} (BanachSpectrum (clopenRationalChart C hC).algebra) :=
  small_of_injective (clopenRationalChart C hC).spectrumMap_injective

end PresentedAffinoidAlgebra

namespace SmallAffinoidSpectrum

variable (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]

/-- A clopen set of a small spectrum represents the corresponding
idempotent chart of the original spectrum. -/
def clopenDomainChart (U : Set (saturated.{u, v} R).presentation.space) (hU : IsClopen U) :
    RationalChart K R :=
  clopenRationalChart (spectrumHomeomorph.{u, v} R ⁻¹' U)
    ⟨hU.1.preimage (spectrumHomeomorph R).continuous,
      hU.2.preimage (spectrumHomeomorph R).continuous⟩

theorem small_clopenDomainChart (U : Set (saturated.{u, v} R).presentation.space)
    (hU : IsClopen U) :
    Small.{v} (BanachSpectrum (clopenDomainChart R U hU).algebra) :=
  small_clopenRationalChart _

attribute [local instance] small_clopenDomainChart

private abbrev localizedSpectrum (A : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum A)] :
    LocalizedCategory.{u, v, v} (K := K) :=
  localizationFunctor.obj (saturated.{u, v} A)

variable (U : Set (saturated.{u, v} R).presentation.space) (hU : IsClopen U)

private abbrev clopenMap :
    localizedSpectrum.{u, v} (clopenDomainChart R U hU).algebra ⟶ localizedSpectrum.{u, v} R :=
  localizedMapEquiv.{u, v} R (clopenDomainChart R U hU).algebra
    (clopenDomainChart R U hU).baseMap

private theorem clopenMap_mono : Mono (clopenMap R U hU) := by
  let d := clopenDomainChart R U hU
  let i := BoundedAlgHom.id K d.algebra
  let f := CommRingCat.ofHom d.baseMap.toAlgHom.toRingHom
  let : Epi f := ConcreteCategory.epi_of_surjective f (surjective_clopenRationalChart _)
  have h : IsPushout f f (𝟙 _) (𝟙 _) :=
    IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  have hp := localized_isPullback_of_ring_isPushout.{u, v}
    (f := d.baseMap) (g := d.baseMap) (s := i) (t := i) h (BoundedAlgHom.isFiniteBanach_id)
  dsimp only [i] at hp
  rw [map_id, localizationFunctor.map_id] at hp
  exact PullbackCone.mono_of_isLimitMkIdId _ hp.isLimit

private theorem clopenMap_etale : etale (clopenMap R U hU) :=
  map_etale_of_finite_pointwiseEtale
    (clopenDomainChart R U hU).baseMap AffinoidPushout.finiteBanachPushout
    AffinoidPushout.finiteTensorComparison (isFiniteBanach_clopenRationalChart _)
    (algebraicallyFiniteEtale_clopenRationalChart _).isEtaleAtPoint

private theorem range_clopenMap :
    range (localizedSpaceFunctor.map (clopenMap R U hU)) = U := by
  let d := clopenDomainChart R U hU
  have hmap (t : BanachSpectrum d.algebra) :
      localizedSpaceFunctor.map (clopenMap R U hU) (spectrumHomeomorph.{u, v} d.algebra t) =
        spectrumHomeomorph.{u, v} R (d.spectrumMap t) :=
    map_spectrumHomeomorph d.baseMap t
  have hloc : d.locus = spectrumHomeomorph.{u, v} R ⁻¹' U := locus_clopenRationalChart _ _
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := (spectrumHomeomorph.{u, v} d.algebra).surjective z
    rw [hmap]
    have ht : d.spectrumMap t ∈ d.locus := d.range_spectrumMap ▸ mem_range_self t
    change d.spectrumMap t ∈ spectrumHomeomorph.{u, v} R ⁻¹' U
    rwa [← hloc]
  · intro hy
    obtain ⟨x, rfl⟩ := (spectrumHomeomorph.{u, v} R).surjective y
    have hx : x ∈ range d.spectrumMap := by rw [d.range_spectrumMap, hloc]; exact hy
    obtain ⟨t, ht⟩ := hx
    exact ⟨spectrumHomeomorph.{u, v} d.algebra t, (hmap t).trans (congrArg _ ht)⟩

private theorem eqToHom_domainι {Y : LocalizedCategory.{u, v, v} (K := K)}
    {D E : (presentationOf Y).AnalyticDomain} (h : D = E) :
    eqToHom (congrArg (domainObj Y) h) ≫ domainι Y E = domainι Y D := by
  subst E
  simp

private theorem clopenImageDomain_eq :
    etaleImageDomain (clopenMap R U hU) (clopenMap_etale R U hU) =
      (presentationOf (localizedSpectrum.{u, v} R)).openDomain U hU.2 :=
  SetLike.coe_injective (range_clopenMap R U hU)

/-- A clopen analytic domain in a small affinoid is the small spectrum of
its idempotent chart. -/
def clopenDomainIso :
    localizedSpectrum.{u, v} (clopenDomainChart R U hU).algebra ≅
      domainObj (localizedSpectrum.{u, v} R) ((presentationOf (localizedSpectrum.{u, v} R)).openDomain U hU.2) :=
  let : Mono (clopenMap R U hU) := clopenMap_mono R U hU
  etaleMonoImageIso (clopenMap R U hU) (clopenMap_etale R U hU) ≪≫
    eqToIso (congrArg (domainObj (localizedSpectrum.{u, v} R)) (clopenImageDomain_eq R U hU))

theorem clopenDomainIso_hom_comp_domainι :
    (clopenDomainIso R U hU).hom ≫
      domainι (localizedSpectrum.{u, v} R)
        ((presentationOf (localizedSpectrum.{u, v} R)).openDomain U hU.2) =
      localizedMapEquiv.{u, v} R (clopenDomainChart R U hU).algebra
        (clopenDomainChart R U hU).baseMap := by
  have : Mono (clopenMap R U hU) := clopenMap_mono R U hU
  change ((etaleMonoImageIso (clopenMap R U hU) (clopenMap_etale R U hU)).hom ≫
      eqToHom (congrArg (domainObj (localizedSpectrum.{u, v} R))
        (clopenImageDomain_eq R U hU))) ≫
    domainι (localizedSpectrum.{u, v} R)
      ((presentationOf (localizedSpectrum.{u, v} R)).openDomain U hU.2) = clopenMap R U hU
  rw [Category.assoc, eqToHom_domainι (clopenImageDomain_eq R U hU),
    etaleMonoImageIso_hom_comp_domainι]

section EtaleMono

variable {X : LocalizedCategory.{u, v, v} (K := K)}
  (f : X ⟶ localizedSpectrum.{u, v} R) (hf : etale f)
  (hImage : range (localizedSpaceFunctor.map f) = U)

include hImage in
private theorem etaleImageDomain_eq_of_range :
    etaleImageDomain f hf = (presentationOf (localizedSpectrum.{u, v} R)).openDomain U hU.2 :=
  SetLike.coe_injective hImage

variable [Mono f]

/-- The source of an étale monomorphism with clopen image in a small affinoid
spectrum is the spectrum of its idempotent chart. -/
def etaleMonoClopenImageIso :
    X ≅ localizedSpectrum.{u, v} (clopenDomainChart R U hU).algebra :=
  etaleMonoImageIso f hf ≪≫
    eqToIso (congrArg (domainObj (localizedSpectrum.{u, v} R))
      (etaleImageDomain_eq_of_range R U hU f hf hImage)) ≪≫
    (clopenDomainIso R U hU).symm

@[reassoc]
theorem etaleMonoClopenImageIso_hom_comp_map :
    (etaleMonoClopenImageIso R U hU f hf hImage).hom ≫
      localizedMapEquiv.{u, v} R (clopenDomainChart R U hU).algebra
        (clopenDomainChart R U hU).baseMap = f := by
  let e := clopenDomainIso R U hU
  let hD := etaleImageDomain_eq_of_range R U hU f hf hImage
  change ((etaleMonoImageIso f hf).hom ≫ eqToHom
    (congrArg (domainObj (localizedSpectrum.{u, v} R)) hD) ≫ e.inv) ≫ _ = f
  rw [← clopenDomainIso_hom_comp_domainι R U hU, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, eqToHom_domainι hD]
  exact etaleMonoImageIso_hom_comp_domainι f hf

end EtaleMono

end SmallAffinoidSpectrum

end Langlands.Analytic
