import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantRestriction
import Langlands.Topology.GroupAction.CompactLocallyConstantFunctor

/-! # Continuous equivariant locally constant presheaves on weighted rational charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology CompactAction

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- The original invariant locus diagram has compact actual subspace topologies. -/
def normInvariantCompactLocusFunctor (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ CompactContinuousAction.{u, v} H :=
  ObjectProperty.lift _ (normInvariantLocusFunctor ρ hρ H) (fun d =>
    isCompact_iff_compactSpace.mp
      (RationalPresentation.isCompact_locus K A d.obj.radii d.obj.denominator d.obj.numerators))

/-- Every original chart restriction gives inverse-image pullback of the entire
locally constant function set, with its derived discrete continuous action. -/
def normInvariantLocusLocallyConstantPresheaf (H : OpenSubgroup G) (C : Type w) :
    (NormInvariantChart ρ hρ H)ᵒᵖ ⥤ ContAction TopCat.{max u w} H :=
  (normInvariantCompactLocusFunctor ρ hρ H).op ⋙
    CompactContinuousAction.locallyConstantFunctor H C

@[simp]
theorem normInvariantLocusLocallyConstantPresheaf_action_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) {C : Type w} (g : H)
    (f : DiscreteLocallyConstant d.obj.locus C) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant (ConcreteCategory.hom
      (((normInvariantLocusLocallyConstantPresheaf ρ hρ H C).obj (Opposite.op d)).obj.ρ g)
        f)) x =
      f (ConcreteCategory.hom ((normInvariantLocusAction ρ hρ H d).obj.ρ g⁻¹) x) := rfl

@[simp]
theorem normInvariantLocusLocallyConstantPresheaf_map_apply (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (q : d ⟶ e) {C : Type w}
    (f : DiscreteLocallyConstant e.obj.locus C) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((normInvariantLocusLocallyConstantPresheaf ρ hρ H C).map q.op).hom.hom f)) x =
        f (q.hom.locusMap x) := rfl

variable [CompleteSpace K]

/-- The unchanged actual rational quotient spectra form a compact action diagram. -/
def normInvariantCompactSpectrumFunctor (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ CompactContinuousAction.{u, v} H :=
  ObjectProperty.lift _ (normInvariantSpectrumFunctor ρ hρ H) (fun d =>
    (inferInstance : CompactSpace (BanachSpectrum d.obj.algebra)))

/-- Locally constant functions on every original quotient spectrum and every
original bounded restriction, with their actual continuous common-subgroup actions. -/
def normInvariantSpectrumLocallyConstantPresheaf (H : OpenSubgroup G) (C : Type w) :
    (NormInvariantChart ρ hρ H)ᵒᵖ ⥤ ContAction TopCat.{max u w} H :=
  (normInvariantCompactSpectrumFunctor ρ hρ H).op ⋙
    CompactContinuousAction.locallyConstantFunctor H C

@[simp]
theorem normInvariantSpectrumLocallyConstantPresheaf_action_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) {C : Type w} (g : H)
    (f : DiscreteLocallyConstant (BanachSpectrum d.obj.algebra) C)
    (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant (ConcreteCategory.hom
      (((normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C).obj (Opposite.op d)).obj.ρ g)
        f)) x =
      f (BanachSpectrum.comap
        ((normInvariantSectionAction ρ hρ H d).actionAut g⁻¹).inv.toBoundedRingHom x) := rfl

@[simp]
theorem normInvariantSpectrumLocallyConstantPresheaf_map_apply (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (q : d ⟶ e) {C : Type w}
    (f : DiscreteLocallyConstant (BanachSpectrum e.obj.algebra) C)
    (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C).map q.op).hom.hom f)) x =
        f (q.hom.spectrumMap x) := rfl

/-- Lift the original natural rational homeomorphism, with both existing maps. -/
def normInvariantCompactSpectrumLocusIso (H : OpenSubgroup G) :
    normInvariantCompactSpectrumFunctor ρ hρ H ≅ normInvariantCompactLocusFunctor ρ hρ H :=
  NatIso.ofComponents (fun d => ObjectProperty.isoMk _
    ((normInvariantSpectrumLocusIso ρ hρ H).app d)) (fun q => by
      apply ObjectProperty.hom_ext _
      exact (normInvariantSpectrumLocusIso ρ hρ H).hom.naturality q)

/-- The original rational homeomorphism gives a natural isomorphism of the
entire discrete continuous locally constant function presheaves. -/
def normInvariantLocallyConstantPresheafIso (H : OpenSubgroup G) (C : Type w) :
    normInvariantLocusLocallyConstantPresheaf ρ hρ H C ≅
      normInvariantSpectrumLocallyConstantPresheaf ρ hρ H C :=
  Functor.isoWhiskerRight (NatIso.op (normInvariantCompactSpectrumLocusIso ρ hρ H))
    (CompactContinuousAction.locallyConstantFunctor H C)

@[simp]
theorem normInvariantLocallyConstantPresheafIso_hom_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) {C : Type w}
    (f : DiscreteLocallyConstant d.obj.locus C) (x : BanachSpectrum d.obj.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((normInvariantLocallyConstantPresheafIso ρ hρ H C).hom.app (Opposite.op d)).hom.hom f)) x =
        f (d.obj.locusHomeomorph x) := rfl

@[simp]
theorem normInvariantLocallyConstantPresheafIso_inv_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) {C : Type w}
    (f : DiscreteLocallyConstant (BanachSpectrum d.obj.algebra) C) (x : d.obj.locus) :
    (DiscreteLocallyConstant.toLocallyConstant
      (((normInvariantLocallyConstantPresheafIso ρ hρ H C).inv.app (Opposite.op d)).hom.hom f)) x =
        f (d.obj.locusHomeomorph.symm x) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
