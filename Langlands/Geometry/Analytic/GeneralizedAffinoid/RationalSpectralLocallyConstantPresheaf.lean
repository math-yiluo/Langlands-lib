import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantRestriction
import Langlands.Topology.GroupAction.CompactLocallyConstantFunctor

/-! # Continuous equivariant locally constant presheaves on spectral-invariant rational charts -/

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

/-- The original invariant locus diagram has compact actual subspace topologies. -/
def spectralInvariantCompactLocusFunctor (H : OpenSubgroup G) :
    SpectralInvariantChart ρ H ⥤ CompactContinuousAction.{u, v} H :=
  ObjectProperty.lift _ (spectralInvariantLocusFunctor ρ H) (fun d =>
    isCompact_iff_compactSpace.mp
      (RationalPresentation.isCompact_locus K A d.obj.radii d.obj.denominator d.obj.numerators))

/-- Every original chart restriction gives inverse-image pullback of the entire
locally constant function set, with its derived discrete continuous action. -/
def spectralInvariantLocusLocallyConstantPresheaf (H : OpenSubgroup G) (C : Type w) :
    (SpectralInvariantChart ρ H)ᵒᵖ ⥤ ContAction TopCat.{max u w} H :=
  (spectralInvariantCompactLocusFunctor ρ H).op ⋙
    CompactContinuousAction.locallyConstantFunctor H C

@[simp]
theorem spectralInvariantLocusLocallyConstantPresheaf_action_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) {C : Type w} (g : H)
    (f : DiscreteLocallyConstant d.obj.locus C) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant (ConcreteCategory.hom
      (((spectralInvariantLocusLocallyConstantPresheaf ρ H C).obj (Opposite.op d)).obj.ρ g)
        f)) x =
      f (ConcreteCategory.hom (((spectralInvariantLocusFunctor ρ H).obj d).obj.ρ g⁻¹) x) := rfl

@[simp]
theorem spectralInvariantLocusLocallyConstantPresheaf_map_apply (H : OpenSubgroup G)
    {d e : SpectralInvariantChart ρ H} (q : d ⟶ e) {C : Type w}
    (f : DiscreteLocallyConstant e.obj.locus C) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((spectralInvariantLocusLocallyConstantPresheaf ρ H C).map q.op).hom.hom f)) x =
        f (q.hom.locusMap x) := rfl

/-- The unchanged actual rational quotient spectra form a compact action diagram. -/
def spectralInvariantCompactSpectrumFunctor (H : OpenSubgroup G) :
    SpectralInvariantChart ρ H ⥤ CompactContinuousAction.{u, v} H :=
  ObjectProperty.lift _ (spectralInvariantSpectrumFunctor ρ H) (fun d =>
    (inferInstance : CompactSpace (BanachSpectrum d.obj.algebra)))

/-- Locally constant functions on every original quotient spectrum and every
original bounded restriction, with their actual continuous common-subgroup actions. -/
def spectralInvariantSpectrumLocallyConstantPresheaf (H : OpenSubgroup G) (C : Type w) :
    (SpectralInvariantChart ρ H)ᵒᵖ ⥤ ContAction TopCat.{max u w} H :=
  (spectralInvariantCompactSpectrumFunctor ρ H).op ⋙
    CompactContinuousAction.locallyConstantFunctor H C

@[simp]
theorem spectralInvariantSpectrumLocallyConstantPresheaf_action_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) {C : Type w} (g : H)
    (f : DiscreteLocallyConstant (BanachSpectrum d.obj.algebra) C)
    (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant (ConcreteCategory.hom
      (((spectralInvariantSpectrumLocallyConstantPresheaf ρ H C).obj (Opposite.op d)).obj.ρ g)
        f)) x =
      f (BanachSpectrum.comap
        ((spectralInvariantSectionAction ρ H d).actionAut g⁻¹).inv.toBoundedRingHom x) := rfl

@[simp]
theorem spectralInvariantSpectrumLocallyConstantPresheaf_map_apply (H : OpenSubgroup G)
    {d e : SpectralInvariantChart ρ H} (q : d ⟶ e) {C : Type w}
    (f : DiscreteLocallyConstant (BanachSpectrum e.obj.algebra) C)
    (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((spectralInvariantSpectrumLocallyConstantPresheaf ρ H C).map q.op).hom.hom f)) x =
        f (q.hom.spectrumMap x) := rfl

/-- Lift the original natural rational homeomorphism, with both existing maps. -/
def spectralInvariantCompactSpectrumLocusIso (H : OpenSubgroup G) :
    spectralInvariantCompactSpectrumFunctor ρ H ≅ spectralInvariantCompactLocusFunctor ρ H :=
  NatIso.ofComponents (fun d => ObjectProperty.isoMk _
    ((spectralInvariantSpectrumLocusIso ρ H).app d)) (fun q => by
      apply ObjectProperty.hom_ext _
      exact (spectralInvariantSpectrumLocusIso ρ H).hom.naturality q)

/-- The original rational homeomorphism gives a natural isomorphism of the
entire discrete continuous locally constant function presheaves. -/
def spectralInvariantLocallyConstantPresheafIso (H : OpenSubgroup G) (C : Type w) :
    spectralInvariantLocusLocallyConstantPresheaf ρ H C ≅
      spectralInvariantSpectrumLocallyConstantPresheaf ρ H C :=
  Functor.isoWhiskerRight (NatIso.op (spectralInvariantCompactSpectrumLocusIso ρ H))
    (CompactContinuousAction.locallyConstantFunctor H C)

@[simp]
theorem spectralInvariantLocallyConstantPresheafIso_hom_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) {C : Type w}
    (f : DiscreteLocallyConstant d.obj.locus C) (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((spectralInvariantLocallyConstantPresheafIso ρ H C).hom.app (Opposite.op d)).hom.hom f)) x =
        f (d.obj.locusHomeomorph x) := rfl

@[simp]
theorem spectralInvariantLocallyConstantPresheafIso_inv_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) {C : Type w}
    (f : DiscreteLocallyConstant (BanachSpectrum d.obj.algebra) C) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((spectralInvariantLocallyConstantPresheafIso ρ H C).inv.app (Opposite.op d)).hom.hom f)) x =
        f (d.obj.locusHomeomorph.symm x) := rfl

/-- Changing chart invariance and restricting the acting group retain exactly
all original locus functions, their actions and every pullback map. -/
theorem spectralInvariantLocusLocallyConstantPresheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (spectralInvariantChartRestriction ρ h).op ⋙
        spectralInvariantLocusLocallyConstantPresheaf ρ H C =
      spectralInvariantLocusLocallyConstantPresheaf ρ J C ⋙
        ContAction.res TopCat.{max u w} (openSubgroupInclusion h) := rfl

/-- The same subgroup identity retains every original quotient-spectrum
function and every original bounded restriction map. -/
theorem spectralInvariantSpectrumLocallyConstantPresheaf_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    (spectralInvariantChartRestriction ρ h).op ⋙
        spectralInvariantSpectrumLocallyConstantPresheaf ρ H C =
      spectralInvariantSpectrumLocallyConstantPresheaf ρ J C ⋙
        ContAction.res TopCat.{max u w} (openSubgroupInclusion h) := rfl

/-- Both subgroup routes retain the same natural comparison, including
pullback along the original homeomorphism and its inverse. -/
theorem spectralInvariantLocallyConstantPresheafIso_subgroup
    {H J : OpenSubgroup G} (h : H ≤ J) (C : Type w) :
    Functor.isoWhiskerLeft (spectralInvariantChartRestriction ρ h).op
        (spectralInvariantLocallyConstantPresheafIso ρ H C) =
      Functor.isoWhiskerRight (spectralInvariantLocallyConstantPresheafIso ρ J C)
        (ContAction.res TopCat.{max u w} (openSubgroupInclusion h)) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
