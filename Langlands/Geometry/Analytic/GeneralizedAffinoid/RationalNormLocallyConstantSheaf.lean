import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantRestrictionSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormLocallyConstantPresheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartLocallyConstantSheaf

/-! # Continuous-action-valued locally constant sheaves on weighted rational sites -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology CompactAction
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- Forgetting actions and the discrete wrapper recovers all original locus functions. -/
def normInvariantLocusLocallyConstantForgetIso (H : OpenSubgroup G) (C : Type w) :
    normInvariantLocusLocallyConstantPresheaf ρ hρ H C ⋙
        forget (ContAction TopCat.{max u w} H) ≅
      (normInvariantChartInclusion ρ hρ H).op ⋙ locusLocallyConstantPresheaf K A C :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom DiscreteLocallyConstant.toLocallyConstant
      inv := TypeCat.ofHom DiscreteLocallyConstant.mk
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

variable [CompleteSpace K]

/-- Forgetting the spectrum actions recovers the ordinary presheaf on the
unchanged original rational quotient spectra. -/
def normInvariantSpectrumLocallyConstantForgetIso (H : OpenSubgroup G) (C : Type w) :
    normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C ⋙
        forget (ContAction TopCat.{max u w} H) ≅
      (normInvariantChartInclusion ρ hρ H).op ⋙ spectrumLocallyConstantPresheaf K A C :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom DiscreteLocallyConstant.toLocallyConstant
      inv := TypeCat.ofHom DiscreteLocallyConstant.mk
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

/-- The comparison after forgetting actions is precisely the original ordinary
spectrum-locus comparison, with the discrete wrappers removed. -/
theorem normInvariantLocallyConstantPresheafIso_forget
    (H : OpenSubgroup G) (C : Type w) :
    Functor.isoWhiskerRight (normInvariantLocallyConstantPresheafIso ρ hρ H C)
          (forget (ContAction TopCat.{max u w} H)) ≪≫
        normInvariantSpectrumLocallyConstantForgetIso ρ hρ H C =
      normInvariantLocusLocallyConstantForgetIso ρ hρ H C ≪≫
        Functor.isoWhiskerLeft (normInvariantChartInclusion ρ hρ H).op
          (locallyConstantPresheafIso K A C) := rfl

/-- The actual underlying function presheaf is a sheaf by site continuity. -/
theorem normInvariantLocusLocallyConstantForget_isSheaf (H : OpenSubgroup G) (C : Type w) :
    Presheaf.IsSheaf (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (normInvariantLocusLocallyConstantPresheaf ρ hρ H C ⋙
        forget (ContAction TopCat.{max u w} H)) :=
  (Presheaf.isSheaf_of_iso_iff
    (normInvariantLocusLocallyConstantForgetIso ρ hρ H C)).mpr
      ((normInvariantChartInclusion ρ hρ H).op_comp_isSheaf_of_isSheaf
        (NormInvariantChart.finiteRationalTopology ρ hρ H) (finiteRationalTopology K A)
        (locusLocallyConstantPresheaf K A C) (locusLocallyConstantPresheaf_isSheaf K A C))

/-- On the actual finite rational site, discrete continuous-action presheaves
are sheaves whenever their underlying sets are sheaves. Finite covers ensure
that pointwise gluing is continuous. -/
theorem normInvariantDiscretePresheaf_isSheaf (H : OpenSubgroup G)
    (F : (NormInvariantChart ρ hρ H)ᵒᵖ ⥤ ContAction TopCat.{w} H)
    [∀ d, DiscreteTopology (F.obj d).obj.V]
    (hF : Presheaf.IsSheaf (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (F ⋙ forget (ContAction TopCat.{w} H))) :
    Presheaf.IsSheaf (NormInvariantChart.finiteRationalTopology ρ hρ H) F := by
  let U := F ⋙ forget (ContAction TopCat.{w} H)
  have hU : Presieve.IsSheaf (NormInvariantChart.finiteRationalTopology ρ hρ H) U :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hF
  intro E d S hS p hp
  let pAt (x : E.obj.V) : Presieve.FamilyOfElements U S.arrows :=
    fun _ f hf => (p f hf).hom.hom x
  have hpAt (x : E.obj.V) : (pAt x).Compatible := by
    intro e e' t a b f g hf hg hab
    exact congrArg (fun k => k.hom.hom x) (hp a b hf hg hab)
  let q : E.obj.V → (F.obj (Opposite.op d)).obj.V :=
    fun x => (hU S hS).amalgamate (pAt x) (hpAt x)
  have hq {e : NormInvariantChart ρ hρ H} (f : e ⟶ d) (hf : S f) (x : E.obj.V) :
      (F.map f.op).hom.hom (q x) = (p f hf).hom.hom x :=
    (hU S hS).valid_glue (hpAt x) f hf
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  let : Finite I := hI
  have hfinite : Sieve.ofArrows D f ∈ NormInvariantChart.finiteRationalTopology ρ hρ H d :=
    (NormInvariantChart.ofArrows_mem_finiteRationalTopology_iff ρ hρ H D f).mpr hcover
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
theorem normInvariantLocusLocallyConstantPresheaf_isSheaf
    (H : OpenSubgroup G) (C : Type w) :
    Presheaf.IsSheaf (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (normInvariantLocusLocallyConstantPresheaf ρ hρ H C) := by
  let (d : (NormInvariantChart ρ hρ H)ᵒᵖ) :
      DiscreteTopology
        ((normInvariantLocusLocallyConstantPresheaf ρ hρ H C).obj d).obj.V :=
    inferInstanceAs (DiscreteTopology (DiscreteLocallyConstant d.unop.obj.locus C))
  exact normInvariantDiscretePresheaf_isSheaf ρ hρ H _
    (normInvariantLocusLocallyConstantForget_isSheaf ρ hρ H C)

/-- The original natural equivariant homeomorphism transports sheafness to
the full locally constant presheaf on the original quotient spectra. -/
theorem normInvariantSpectrumLocallyConstantPresheaf_isSheaf
    (H : OpenSubgroup G) (C : Type w) :
    Presheaf.IsSheaf (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C) :=
  (Presheaf.isSheaf_of_iso_iff
    (normInvariantLocallyConstantPresheafIso ρ hρ H C)).mp
      (normInvariantLocusLocallyConstantPresheaf_isSheaf ρ hρ H C)

/-- All locally constant functions on the actual invariant loci, with their
proved discrete continuous actions and actual restrictions, form a sheaf. -/
def normInvariantLocusLocallyConstantSheaf (H : OpenSubgroup G) (C : Type w) :
    Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (ContAction TopCat.{max u w} H) :=
  ⟨normInvariantLocusLocallyConstantPresheaf ρ hρ H C,
    normInvariantLocusLocallyConstantPresheaf_isSheaf ρ hρ H C⟩

/-- All locally constant functions on the original invariant quotient spectra,
with their proved discrete continuous actions, form a sheaf. -/
def normInvariantSpectrumLocallyConstantSheaf (H : OpenSubgroup G) (C : Type w) :
    Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ H)
      (ContAction TopCat.{max u w} H) :=
  ⟨normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C,
    normInvariantSpectrumLocallyConstantPresheaf_isSheaf ρ hρ H C⟩

/-- The original natural equivariant spectrum-locus homeomorphism induces an
isomorphism of the constructed continuous-action-valued sheaves. -/
def normInvariantLocallyConstantSheafIso (H : OpenSubgroup G) (C : Type w) :
    normInvariantLocusLocallyConstantSheaf ρ hρ H C ≅
      normInvariantSpectrumLocallyConstantSheaf ρ hρ H C :=
  ObjectProperty.isoMk _ (normInvariantLocallyConstantPresheafIso ρ hρ H C)

omit [CompleteSpace K] in
/-- Changing the chart invariance subgroup and restricting the acting group
retain exactly the same locus functions, actions and restriction maps. -/
theorem normInvariantLocusLocallyConstantPresheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (normInvariantChartRestriction ρ hρ h).op ⋙
        normInvariantLocusLocallyConstantPresheaf ρ hρ H C =
      normInvariantLocusLocallyConstantPresheaf ρ hρ J C ⋙
        ContAction.res TopCat.{max u w} (openSubgroupInclusion h) := rfl

/-- The subgroup identity also retains every original quotient-spectrum function
and every original bounded restriction map. -/
theorem normInvariantSpectrumLocallyConstantPresheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (normInvariantChartRestriction ρ hρ h).op ⋙
        normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C =
      normInvariantSpectrumLocallyConstantPresheaf ρ hρ J C ⋙
        ContAction.res TopCat.{max u w} (openSubgroupInclusion h) := rfl

/-- Both subgroup routes retain the same natural spectrum-locus comparison,
including its original inverse maps. -/
theorem normInvariantLocallyConstantPresheafIso_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    Functor.isoWhiskerLeft (normInvariantChartRestriction ρ hρ h).op
        (normInvariantLocallyConstantPresheafIso ρ hρ H C) =
      Functor.isoWhiskerRight (normInvariantLocallyConstantPresheafIso ρ hρ J C)
        (ContAction.res TopCat.{max u w} (openSubgroupInclusion h)) := rfl

/-- The original J-locus presheaf, with action restricted to H, is a sheaf
on the J-invariant site by continuity of the actual chart inclusion. -/
def normInvariantLocusLocallyConstantRestrictedSheaf
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ J)
      (ContAction TopCat.{max u w} H) :=
  ⟨normInvariantLocusLocallyConstantPresheaf ρ hρ J C ⋙
      ContAction.res TopCat.{max u w} (openSubgroupInclusion h), by
    rw [← normInvariantLocusLocallyConstantPresheaf_subgroup ρ hρ h C]
    exact ((normInvariantSheafRestriction ρ hρ h (ContAction TopCat.{max u w} H)).obj
      (normInvariantLocusLocallyConstantSheaf ρ hρ H C)).property⟩

/-- The same restricted sheaf on the original quotient spectra. -/
def normInvariantSpectrumLocallyConstantRestrictedSheaf
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    Sheaf (NormInvariantChart.finiteRationalTopology ρ hρ J)
      (ContAction TopCat.{max u w} H) :=
  ⟨normInvariantSpectrumLocallyConstantPresheaf ρ hρ J C ⋙
      ContAction.res TopCat.{max u w} (openSubgroupInclusion h), by
    rw [← normInvariantSpectrumLocallyConstantPresheaf_subgroup ρ hρ h C]
    exact ((normInvariantSheafRestriction ρ hρ h (ContAction TopCat.{max u w} H)).obj
      (normInvariantSpectrumLocallyConstantSheaf ρ hρ H C)).property⟩

/-- The sheaf restriction along the chart inclusion equals restriction of the
original common-subgroup action on the unchanged locus functions. -/
theorem normInvariantLocusLocallyConstantSheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (normInvariantSheafRestriction ρ hρ h (ContAction TopCat.{max u w} H)).obj
        (normInvariantLocusLocallyConstantSheaf ρ hρ H C) =
      normInvariantLocusLocallyConstantRestrictedSheaf ρ hρ h C := rfl

/-- The sheaf restriction also retains the original quotient-spectrum functions. -/
theorem normInvariantSpectrumLocallyConstantSheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (normInvariantSheafRestriction ρ hρ h (ContAction TopCat.{max u w} H)).obj
        (normInvariantSpectrumLocallyConstantSheaf ρ hρ H C) =
      normInvariantSpectrumLocallyConstantRestrictedSheaf ρ hρ h C := rfl

/-- The original natural comparison identifies the two restricted sheaves. -/
def normInvariantLocallyConstantRestrictedSheafIso
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    normInvariantLocusLocallyConstantRestrictedSheaf ρ hρ h C ≅
      normInvariantSpectrumLocallyConstantRestrictedSheaf ρ hρ h C :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (normInvariantLocallyConstantPresheafIso ρ hρ J C)
      (ContAction.res TopCat.{max u w} (openSubgroupInclusion h)))

/-- Chart restriction and action restriction give exactly the same sheaf
comparison, as well as the same underlying original homeomorphisms. -/
theorem normInvariantLocallyConstantSheafIso_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (normInvariantSheafRestriction ρ hρ h (ContAction TopCat.{max u w} H)).mapIso
        (normInvariantLocallyConstantSheafIso ρ hρ H C) =
      normInvariantLocallyConstantRestrictedSheafIso ρ hρ h C := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
