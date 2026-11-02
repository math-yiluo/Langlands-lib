import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantRestrictionSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralLocallyConstantPresheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartLocallyConstantSheaf
import Langlands.Representation.LocallyConstant.CompactAction

/-! # Smooth module-valued locally constant sheaves on spectral-invariant rational charts -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v r w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits Topology CompactAction DomainAutomorphism

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)
  {R : Type r} [CommRing R]

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- All locally constant functions on the original invariant loci, with the
proved smooth diagonal action on arbitrary smooth module coefficients. -/
def spectralInvariantLocusLocallyConstantSmoothPresheaf (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    (SpectralInvariantChart ρ H)ᵒᵖ ⥤ SmoothRep.{r, v, max u w} R H :=
  (spectralInvariantCompactLocusFunctor ρ H).op ⋙
    CompactContinuousAction.locallyConstantModuleFunctor M

/-- All locally constant functions on the unchanged original quotient spectra,
with the original bounded restrictions and smooth diagonal action. -/
def spectralInvariantSpectrumLocallyConstantSmoothPresheaf (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    (SpectralInvariantChart ρ H)ᵒᵖ ⥤ SmoothRep.{r, v, max u w} R H :=
  (spectralInvariantCompactSpectrumFunctor ρ H).op ⋙
    CompactContinuousAction.locallyConstantModuleFunctor M

@[simp]
theorem spectralInvariantLocusLocallyConstantSmoothPresheaf_action_apply
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H)
    (d : SpectralInvariantChart ρ H) (g : H)
    (f : LocallyConstant d.obj.locus M) (x : d.obj.locus) :
    LocallyConstant.toFun
      (((spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M).obj
        (Opposite.op d)).representation g f) x =
      M.representation g
        (f (ConcreteCategory.hom
          (((spectralInvariantLocusFunctor ρ H).obj d).obj.ρ g⁻¹) x)) := rfl

@[simp]
theorem spectralInvariantSpectrumLocallyConstantSmoothPresheaf_action_apply
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H)
    (d : SpectralInvariantChart ρ H) (g : H)
    (f : LocallyConstant (BanachSpectrum d.obj.algebra) M)
    (x : BanachSpectrum d.obj.algebra) :
    LocallyConstant.toFun
      (((spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M).obj
        (Opposite.op d)).representation g f) x =
      M.representation g
        (f (BanachSpectrum.comap
          ((spectralInvariantSectionAction ρ H d).actionAut g⁻¹).inv.toBoundedRingHom x)) :=
  rfl

@[simp]
theorem spectralInvariantLocusLocallyConstantSmoothPresheaf_map_apply
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H)
    {d e : SpectralInvariantChart ρ H} (q : d ⟶ e)
    (f : LocallyConstant e.obj.locus M) (x : d.obj.locus) :
    LocallyConstant.toFun (SmoothRep.hom
      ((spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M).map q.op) f) x =
        f (q.hom.locusMap x) := rfl

@[simp]
theorem spectralInvariantSpectrumLocallyConstantSmoothPresheaf_map_apply
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H)
    {d e : SpectralInvariantChart ρ H} (q : d ⟶ e)
    (f : LocallyConstant (BanachSpectrum e.obj.algebra) M)
    (x : BanachSpectrum d.obj.algebra) :
    LocallyConstant.toFun (SmoothRep.hom
      ((spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M).map q.op) f) x =
        f (q.hom.spectrumMap x) := rfl

/-- Pullback by the actual equivariant rational homeomorphism identifies the
entire smooth diagonal module presheaves. -/
def spectralInvariantLocallyConstantSmoothPresheafIso (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M ≅
      spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M :=
  Functor.isoWhiskerRight (NatIso.op (spectralInvariantCompactSpectrumLocusIso ρ H))
    (CompactContinuousAction.locallyConstantModuleFunctor M)

@[simp]
theorem spectralInvariantLocallyConstantSmoothPresheafIso_hom_apply
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H)
    (d : SpectralInvariantChart ρ H) (f : LocallyConstant d.obj.locus M)
    (x : BanachSpectrum d.obj.algebra) :
    LocallyConstant.toFun (SmoothRep.hom
      ((spectralInvariantLocallyConstantSmoothPresheafIso ρ H M).hom.app
        (Opposite.op d)) f) x = f (d.obj.locusHomeomorph x) := rfl

@[simp]
theorem spectralInvariantLocallyConstantSmoothPresheafIso_inv_apply
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H)
    (d : SpectralInvariantChart ρ H)
    (f : LocallyConstant (BanachSpectrum d.obj.algebra) M) (x : d.obj.locus) :
    LocallyConstant.toFun (SmoothRep.hom
      ((spectralInvariantLocallyConstantSmoothPresheafIso ρ H M).inv.app
        (Opposite.op d)) f) x = f (d.obj.locusHomeomorph.symm x) := rfl

/-- Forgetting only module and group structure recovers the original locus
function presheaf on the invariant charts. -/
def spectralInvariantLocusLocallyConstantSmoothForgetIso (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M ⋙
        (SmoothRep.toRep ⋙ forget (Rep.{max u w} R H)) ≅
      (spectralInvariantChartInclusion ρ H).op ⋙ locusLocallyConstantPresheaf K A M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Forgetting only module and group structure recovers the original quotient
spectrum function presheaf with every bounded restriction. -/
def spectralInvariantSpectrumLocallyConstantSmoothForgetIso (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M ⋙
        (SmoothRep.toRep ⋙ forget (Rep.{max u w} R H)) ≅
      (spectralInvariantChartInclusion ρ H).op ⋙ spectrumLocallyConstantPresheaf K A M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The forgotten smooth comparison is exactly pullback by the original
rational homeomorphism and its inverse. -/
theorem spectralInvariantLocallyConstantSmoothPresheafIso_forget
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H) :
    Functor.isoWhiskerRight (spectralInvariantLocallyConstantSmoothPresheafIso ρ H M)
          (SmoothRep.toRep ⋙ forget (Rep.{max u w} R H)) ≪≫
        spectralInvariantSpectrumLocallyConstantSmoothForgetIso ρ H M =
      spectralInvariantLocusLocallyConstantSmoothForgetIso ρ H M ≪≫
        Functor.isoWhiskerLeft (spectralInvariantChartInclusion ρ H).op
          (locallyConstantPresheafIso K A M) := rfl

/-- Site continuity and the ordinary locally constant sheaf prove sheafness of
the unchanged underlying sets of functions. -/
theorem spectralInvariantLocusLocallyConstantSmoothForget_isSheaf
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M ⋙
        (SmoothRep.toRep ⋙ forget (Rep.{max u w} R H))) :=
  (Presheaf.isSheaf_of_iso_iff
    (spectralInvariantLocusLocallyConstantSmoothForgetIso ρ H M)).mpr
      ((spectralInvariantChartInclusion ρ H).op_comp_isSheaf_of_isSheaf
        (SpectralInvariantChart.finiteRationalTopology ρ H) (finiteRationalTopology K A)
        (locusLocallyConstantPresheaf K A M) (locusLocallyConstantPresheaf_isSheaf K A M))

/-- Reflecting the actual matching limits through representations, modules and
sets proves the categorical smooth-representation-valued sheaf condition. -/
theorem spectralInvariantLocusLocallyConstantSmoothPresheaf_isSheaf
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M) := by
  let : ReflectsLimitsOfSize.{u, u}
      (forget₂ (Rep.{max u w} R H) (ModuleCat.{max u w} R)) :=
    reflectsLimitsOfSize_shrink _
  let : ReflectsLimitsOfSize.{u, u} (forget (ModuleCat.{max u w} R)) :=
    ModuleCat.forget_reflectsLimitsOfSize.{w, u}
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ SmoothRep.toRep
  apply Presheaf.isSheaf_of_isSheaf_comp _ _
    (forget₂ (Rep.{max u w} R H) (ModuleCat.{max u w} R))
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{max u w} R))
  exact spectralInvariantLocusLocallyConstantSmoothForget_isSheaf ρ H M

/-- The actual smooth equivariant spectrum-locus isomorphism transports
sheafness to all original quotient-spectrum functions. -/
theorem spectralInvariantSpectrumLocallyConstantSmoothPresheaf_isSheaf
    (H : OpenSubgroup G) (M : SmoothRep.{r, v, w} R H) :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M) :=
  (Presheaf.isSheaf_of_iso_iff
    (spectralInvariantLocallyConstantSmoothPresheafIso ρ H M)).mp
      (spectralInvariantLocusLocallyConstantSmoothPresheaf_isSheaf ρ H M)

/-- The full locally constant locus module sheaf with smooth diagonal action. -/
def spectralInvariantLocusLocallyConstantSmoothSheaf (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (SmoothRep.{r, v, max u w} R H) :=
  ⟨spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M,
    spectralInvariantLocusLocallyConstantSmoothPresheaf_isSheaf ρ H M⟩

/-- The full locally constant quotient-spectrum module sheaf with smooth
diagonal action and the original bounded restrictions. -/
def spectralInvariantSpectrumLocallyConstantSmoothSheaf (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (SmoothRep.{r, v, max u w} R H) :=
  ⟨spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M,
    spectralInvariantSpectrumLocallyConstantSmoothPresheaf_isSheaf ρ H M⟩

/-- The original rational homeomorphism identifies the actual smooth module
sheaves in both directions. -/
def spectralInvariantLocallyConstantSmoothSheafIso (H : OpenSubgroup G)
    (M : SmoothRep.{r, v, w} R H) :
    spectralInvariantLocusLocallyConstantSmoothSheaf ρ H M ≅
      spectralInvariantSpectrumLocallyConstantSmoothSheaf ρ H M :=
  ObjectProperty.isoMk _ (spectralInvariantLocallyConstantSmoothPresheafIso ρ H M)

/-- Postcomposition by every original coefficient intertwiner gives a
covariant functor to the actual locus presheaves. -/
def spectralInvariantLocusLocallyConstantSmoothPresheafCoefficients (H : OpenSubgroup G) :
    SmoothRep.{r, v, w} R H ⥤
      ((SpectralInvariantChart ρ H)ᵒᵖ ⥤ SmoothRep.{r, v, max u w} R H) where
  obj M := spectralInvariantLocusLocallyConstantSmoothPresheaf ρ H M
  map a := Functor.whiskerLeft (spectralInvariantCompactLocusFunctor ρ H).op
    (CompactContinuousAction.locallyConstantModuleCoefficientMap a)
  map_id _ := by
    ext d f
    rfl
  map_comp _ _ := by
    ext d f
    rfl

/-- Coefficient postcomposition on all original quotient-spectrum functions. -/
def spectralInvariantSpectrumLocallyConstantSmoothPresheafCoefficients (H : OpenSubgroup G) :
    SmoothRep.{r, v, w} R H ⥤
      ((SpectralInvariantChart ρ H)ᵒᵖ ⥤ SmoothRep.{r, v, max u w} R H) where
  obj M := spectralInvariantSpectrumLocallyConstantSmoothPresheaf ρ H M
  map a := Functor.whiskerLeft (spectralInvariantCompactSpectrumFunctor ρ H).op
    (CompactContinuousAction.locallyConstantModuleCoefficientMap a)
  map_id _ := by
    ext d f
    rfl
  map_comp _ _ := by
    ext d f
    rfl

@[simp]
theorem spectralInvariantLocusLocallyConstantSmoothPresheafCoefficients_map_apply
    (H : OpenSubgroup G) {M N : SmoothRep.{r, v, w} R H} (a : M ⟶ N)
    (d : SpectralInvariantChart ρ H) (f : LocallyConstant d.obj.locus M)
    (x : d.obj.locus) :
    LocallyConstant.toFun (SmoothRep.hom
      (((spectralInvariantLocusLocallyConstantSmoothPresheafCoefficients ρ H).map a).app
        (Opposite.op d)) f) x = SmoothRep.hom a (f x) := rfl

@[simp]
theorem spectralInvariantSpectrumLocallyConstantSmoothPresheafCoefficients_map_apply
    (H : OpenSubgroup G) {M N : SmoothRep.{r, v, w} R H} (a : M ⟶ N)
    (d : SpectralInvariantChart ρ H)
    (f : LocallyConstant (BanachSpectrum d.obj.algebra) M)
    (x : BanachSpectrum d.obj.algebra) :
    LocallyConstant.toFun (SmoothRep.hom
      (((spectralInvariantSpectrumLocallyConstantSmoothPresheafCoefficients ρ H).map a).app
        (Opposite.op d)) f) x = SmoothRep.hom a (f x) := rfl

/-- The original rational comparison is natural in arbitrary smooth module
coefficients and all equivariant linear maps. -/
def spectralInvariantLocallyConstantSmoothPresheafCoefficientsIso (H : OpenSubgroup G) :
    spectralInvariantLocusLocallyConstantSmoothPresheafCoefficients (R := R) ρ H ≅
      spectralInvariantSpectrumLocallyConstantSmoothPresheafCoefficients ρ H :=
  NatIso.ofComponents (fun M => spectralInvariantLocallyConstantSmoothPresheafIso ρ H M)
    (fun _ => by
      ext d f
      rfl)

/-- The actual smooth locus sheaves form a functor in smooth coefficients. -/
def spectralInvariantLocusLocallyConstantSmoothSheafCoefficients (H : OpenSubgroup G) :
    SmoothRep.{r, v, w} R H ⥤
      Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
        (SmoothRep.{r, v, max u w} R H) :=
  ObjectProperty.lift _
    (spectralInvariantLocusLocallyConstantSmoothPresheafCoefficients ρ H)
    (fun M => spectralInvariantLocusLocallyConstantSmoothPresheaf_isSheaf ρ H M)

/-- The actual smooth quotient-spectrum sheaves form a functor in coefficients. -/
def spectralInvariantSpectrumLocallyConstantSmoothSheafCoefficients (H : OpenSubgroup G) :
    SmoothRep.{r, v, w} R H ⥤
      Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
        (SmoothRep.{r, v, max u w} R H) :=
  ObjectProperty.lift _
    (spectralInvariantSpectrumLocallyConstantSmoothPresheafCoefficients ρ H)
    (fun M => spectralInvariantSpectrumLocallyConstantSmoothPresheaf_isSheaf ρ H M)

/-- The spectrum-locus comparison of actual smooth sheaves is natural in
coefficients, with the original maps in both directions. -/
def spectralInvariantLocallyConstantSmoothSheafCoefficientsIso (H : OpenSubgroup G) :
    spectralInvariantLocusLocallyConstantSmoothSheafCoefficients (R := R) ρ H ≅
      spectralInvariantSpectrumLocallyConstantSmoothSheafCoefficients ρ H :=
  NatIso.ofComponents (fun M => spectralInvariantLocallyConstantSmoothSheafIso ρ H M)
    (fun _ => by
      apply ObjectProperty.hom_ext
      ext d f
      rfl)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
