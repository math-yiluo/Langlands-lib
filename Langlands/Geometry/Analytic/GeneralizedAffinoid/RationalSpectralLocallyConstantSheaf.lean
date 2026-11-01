import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantRestrictionSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralLocallyConstantPresheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartLocallyConstantSheaf

/-! # Continuous-action-valued locally constant sheaves on spectral-invariant rational sites -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology CompactAction DomainAutomorphism
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- Forgetting actions and the discrete wrapper recovers all original locus functions. -/
def spectralInvariantLocusLocallyConstantForgetIso (H : OpenSubgroup G) (C : Type w) :
    spectralInvariantLocusLocallyConstantPresheaf ρ H C ⋙
        forget (ContAction TopCat.{max u w} H) ≅
      (spectralInvariantChartInclusion ρ H).op ⋙ locusLocallyConstantPresheaf K A C :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom DiscreteLocallyConstant.toLocallyConstant
      inv := TypeCat.ofHom DiscreteLocallyConstant.mk
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

/-- Forgetting the spectrum actions recovers the ordinary presheaf on the
unchanged original rational quotient spectra. -/
def spectralInvariantSpectrumLocallyConstantForgetIso (H : OpenSubgroup G) (C : Type w) :
    spectralInvariantSpectrumLocallyConstantPresheaf ρ H C ⋙
        forget (ContAction TopCat.{max u w} H) ≅
      (spectralInvariantChartInclusion ρ H).op ⋙ spectrumLocallyConstantPresheaf K A C :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom DiscreteLocallyConstant.toLocallyConstant
      inv := TypeCat.ofHom DiscreteLocallyConstant.mk
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

/-- The comparison after forgetting actions is precisely the original ordinary
spectrum-locus comparison, with the discrete wrappers removed. -/
theorem spectralInvariantLocallyConstantPresheafIso_forget
    (H : OpenSubgroup G) (C : Type w) :
    Functor.isoWhiskerRight (spectralInvariantLocallyConstantPresheafIso ρ H C)
          (forget (ContAction TopCat.{max u w} H)) ≪≫
        spectralInvariantSpectrumLocallyConstantForgetIso ρ H C =
      spectralInvariantLocusLocallyConstantForgetIso ρ H C ≪≫
        Functor.isoWhiskerLeft (spectralInvariantChartInclusion ρ H).op
          (locallyConstantPresheafIso K A C) := rfl

/-- The actual underlying function presheaf is a sheaf by site continuity. -/
theorem spectralInvariantLocusLocallyConstantForget_isSheaf (H : OpenSubgroup G) (C : Type w) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantLocusLocallyConstantPresheaf ρ H C ⋙
        forget (ContAction TopCat.{max u w} H)) :=
  (Presheaf.isSheaf_of_iso_iff
    (spectralInvariantLocusLocallyConstantForgetIso ρ H C)).mpr
      ((spectralInvariantChartInclusion ρ H).op_comp_isSheaf_of_isSheaf
        (SpectralInvariantChart.finiteRationalTopology ρ H) (finiteRationalTopology K A)
        (locusLocallyConstantPresheaf K A C) (locusLocallyConstantPresheaf_isSheaf K A C))

/-- On the actual finite rational site, discrete continuous-action presheaves
are sheaves whenever their underlying sets are sheaves. Finite covers ensure
that pointwise gluing is continuous. -/
theorem spectralInvariantDiscretePresheaf_isSheaf (H : OpenSubgroup G)
    (F : (SpectralInvariantChart ρ H)ᵒᵖ ⥤ ContAction TopCat.{w} H)
    [∀ d, DiscreteTopology (F.obj d).obj.V]
    (hF : Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (F ⋙ forget (ContAction TopCat.{w} H))) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H) F := by
  let U := F ⋙ forget (ContAction TopCat.{w} H)
  have hU : Presieve.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H) U :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hF
  intro E d S hS p hp
  let pAt (x : E.obj.V) : Presieve.FamilyOfElements U S.arrows :=
    fun _ f hf => (p f hf).hom.hom x
  have hpAt (x : E.obj.V) : (pAt x).Compatible := by
    intro e e' t a b f g hf hg hab
    exact congrArg (fun k => k.hom.hom x) (hp a b hf hg hab)
  let q : E.obj.V → (F.obj (Opposite.op d)).obj.V :=
    fun x => (hU S hS).amalgamate (pAt x) (hpAt x)
  have hq {e : SpectralInvariantChart ρ H} (f : e ⟶ d) (hf : S f) (x : E.obj.V) :
      (F.map f.op).hom.hom (q x) = (p f hf).hom.hom x :=
    (hU S hS).valid_glue (hpAt x) f hf
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  let : Finite I := hI
  have hfinite : Sieve.ofArrows D f ∈ SpectralInvariantChart.finiteRationalTopology ρ H d :=
    (SpectralInvariantChart.ofArrows_mem_finiteRationalTopology_iff ρ H D f).mpr hcover
  let r : (F.obj (Opposite.op d)).obj.V → ∀ i, (F.obj (Opposite.op (D i))).obj.V :=
    fun s i => (F.map (f i).op).hom.hom s
  have hr : Function.Injective r := by
    intro a b hab
    apply (Presieve.isSeparatedFor_iff_generate.mpr
      (hU _ hfinite).isSeparatedFor).ext
    intro e g hg
    cases hg with
    | mk i => exact congrFun hab i
  have hrc : IsEmbedding r :=
    (IsClosedEmbedding.of_continuous_injective_isClosedMap
      continuous_of_discreteTopology hr (fun _ _ => isClosed_discrete _)).isEmbedding
  have hcontinuous : Continuous q := by
    apply hrc.continuous_iff.mpr
    have he : r ∘ q = fun x i => (p (f i) (hf i)).hom.hom x := by
      funext x i
      exact hq (f i) (hf i) x
    rw [he]
    exact continuous_pi fun i => (p (f i) (hf i)).hom.hom.hom.continuous
  let glue : E ⟶ F.obj (Opposite.op d) := ObjectProperty.homMk
    { hom := TopCat.ofHom ⟨q, hcontinuous⟩
      comm := fun g => by
        apply TopCat.ext
        intro x
        apply hr
        funext i
        change (F.map (f i).op).hom.hom (q (ConcreteCategory.hom (E.obj.ρ g) x)) =
          (F.map (f i).op).hom.hom
            (ConcreteCategory.hom ((F.obj (Opposite.op d)).obj.ρ g) (q x))
        have hmap := congrArg (fun k => k (q x)) ((F.map (f i).op).hom.comm g)
        change (F.map (f i).op).hom.hom
            (ConcreteCategory.hom ((F.obj (Opposite.op d)).obj.ρ g) (q x)) =
          ConcreteCategory.hom ((F.obj (Opposite.op (D i))).obj.ρ g)
            ((F.map (f i).op).hom.hom (q x)) at hmap
        rw [hmap, hq, hq]
        exact congrArg (fun k => k x) ((p (f i) (hf i)).hom.comm g) }
  refine ⟨glue, ?_, ?_⟩
  · intro e g hg
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    exact hq g hg x
  · intro other ho
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    apply hr
    funext i
    exact (congrArg (fun k => k.hom.hom x) (ho (f i) (hf i))).trans
      (hq (f i) (hf i) x).symm

/-- The full discrete continuous-action-valued locus presheaf is a sheaf. -/
theorem spectralInvariantLocusLocallyConstantPresheaf_isSheaf
    (H : OpenSubgroup G) (C : Type w) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantLocusLocallyConstantPresheaf ρ H C) := by
  let (d : (SpectralInvariantChart ρ H)ᵒᵖ) :
      DiscreteTopology
        ((spectralInvariantLocusLocallyConstantPresheaf ρ H C).obj d).obj.V :=
    inferInstanceAs (DiscreteTopology (DiscreteLocallyConstant d.unop.obj.locus C))
  exact spectralInvariantDiscretePresheaf_isSheaf ρ H _
    (spectralInvariantLocusLocallyConstantForget_isSheaf ρ H C)

/-- The original natural equivariant homeomorphism transports sheafness to
the full locally constant presheaf on the original quotient spectra. -/
theorem spectralInvariantSpectrumLocallyConstantPresheaf_isSheaf
    (H : OpenSubgroup G) (C : Type w) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantSpectrumLocallyConstantPresheaf ρ H C) :=
  (Presheaf.isSheaf_of_iso_iff
    (spectralInvariantLocallyConstantPresheafIso ρ H C)).mp
      (spectralInvariantLocusLocallyConstantPresheaf_isSheaf ρ H C)

/-- All locally constant functions on the actual invariant loci, with their
proved discrete continuous actions and actual restrictions, form a sheaf. -/
def spectralInvariantLocusLocallyConstantSheaf (H : OpenSubgroup G) (C : Type w) :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (ContAction TopCat.{max u w} H) :=
  ⟨spectralInvariantLocusLocallyConstantPresheaf ρ H C,
    spectralInvariantLocusLocallyConstantPresheaf_isSheaf ρ H C⟩

/-- All locally constant functions on the original invariant quotient spectra,
with their proved discrete continuous actions, form a sheaf. -/
def spectralInvariantSpectrumLocallyConstantSheaf (H : OpenSubgroup G) (C : Type w) :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (ContAction TopCat.{max u w} H) :=
  ⟨spectralInvariantSpectrumLocallyConstantPresheaf ρ H C,
    spectralInvariantSpectrumLocallyConstantPresheaf_isSheaf ρ H C⟩

/-- The original natural equivariant spectrum-locus homeomorphism induces an
isomorphism of the constructed continuous-action-valued sheaves. -/
def spectralInvariantLocallyConstantSheafIso (H : OpenSubgroup G) (C : Type w) :
    spectralInvariantLocusLocallyConstantSheaf ρ H C ≅
      spectralInvariantSpectrumLocallyConstantSheaf ρ H C :=
  ObjectProperty.isoMk _ (spectralInvariantLocallyConstantPresheafIso ρ H C)

/-- The original J-locus presheaf, with action restricted to H, is a sheaf
on the J-invariant site by continuity of the actual chart inclusion. -/
def spectralInvariantLocusLocallyConstantRestrictedSheaf
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ J)
      (ContAction TopCat.{max u w} H) :=
  ⟨spectralInvariantLocusLocallyConstantPresheaf ρ J C ⋙
      ContAction.res TopCat.{max u w} (openSubgroupInclusion h), by
    rw [← spectralInvariantLocusLocallyConstantPresheaf_subgroup ρ h C]
    exact ((spectralInvariantSheafRestriction ρ h (ContAction TopCat.{max u w} H)).obj
      (spectralInvariantLocusLocallyConstantSheaf ρ H C)).property⟩

/-- The same restricted sheaf on the original quotient spectra. -/
def spectralInvariantSpectrumLocallyConstantRestrictedSheaf
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ J)
      (ContAction TopCat.{max u w} H) :=
  ⟨spectralInvariantSpectrumLocallyConstantPresheaf ρ J C ⋙
      ContAction.res TopCat.{max u w} (openSubgroupInclusion h), by
    rw [← spectralInvariantSpectrumLocallyConstantPresheaf_subgroup ρ h C]
    exact ((spectralInvariantSheafRestriction ρ h (ContAction TopCat.{max u w} H)).obj
      (spectralInvariantSpectrumLocallyConstantSheaf ρ H C)).property⟩

/-- The sheaf restriction along the chart inclusion equals restriction of the
original common-subgroup action on the unchanged locus functions. -/
theorem spectralInvariantLocusLocallyConstantSheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (spectralInvariantSheafRestriction ρ h (ContAction TopCat.{max u w} H)).obj
        (spectralInvariantLocusLocallyConstantSheaf ρ H C) =
      spectralInvariantLocusLocallyConstantRestrictedSheaf ρ h C := rfl

/-- The sheaf restriction also retains the original quotient-spectrum functions. -/
theorem spectralInvariantSpectrumLocallyConstantSheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (spectralInvariantSheafRestriction ρ h (ContAction TopCat.{max u w} H)).obj
        (spectralInvariantSpectrumLocallyConstantSheaf ρ H C) =
      spectralInvariantSpectrumLocallyConstantRestrictedSheaf ρ h C := rfl

/-- The original natural comparison identifies the two restricted sheaves. -/
def spectralInvariantLocallyConstantRestrictedSheafIso
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    spectralInvariantLocusLocallyConstantRestrictedSheaf ρ h C ≅
      spectralInvariantSpectrumLocallyConstantRestrictedSheaf ρ h C :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (spectralInvariantLocallyConstantPresheafIso ρ J C)
      (ContAction.res TopCat.{max u w} (openSubgroupInclusion h)))

/-- Chart restriction and action restriction give exactly the same sheaf
comparison, as well as the same underlying original homeomorphisms. -/
theorem spectralInvariantLocallyConstantSheafIso_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (spectralInvariantSheafRestriction ρ h (ContAction TopCat.{max u w} H)).mapIso
        (spectralInvariantLocallyConstantSheafIso ρ H C) =
      spectralInvariantLocallyConstantRestrictedSheafIso ρ h C := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
