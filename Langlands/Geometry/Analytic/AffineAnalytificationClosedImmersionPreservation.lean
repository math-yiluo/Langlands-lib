import Langlands.Geometry.Analytic.AffineAnalytificationQuotientRadii
import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.AtlasTopology.DirectedCompact
import Langlands.Geometry.Analytic.RecognizedFinitePullback
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushout
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # Affine analytification preserves closed immersions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory Set AffinoidAtlasPresentation IndexedAffinoidAtlas
open AnalyticAffineSpace PresentedAffinoidAlgebra SaturatedAtlasPresentation
open LocalizedFunctorialityComparison.OriginalStrongMaps

private theorem isAdmissibleEpi_of_heq {K : Type u} [NormedField K] [IsUltrametricDist K]
    {A B C D : PresentedAffinoidAlgebra K}
    {g : BoundedAlgHom K A B} {g' : BoundedAlgHom K C D}
    (hA : A = C) (hB : B = D) (hg : HEq g g') (h : g'.IsAdmissibleEpi) :
    g.IsAdmissibleEpi := by
  subst C D
  exact (eq_of_heq hg).symm ▸ h

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  {B : Type w} [CommRing B] [Algebra K B] (f : A →ₐ[K] B) (hf : Function.Surjective f)

local notation "Q" => quotientPolynomialPresentation K P f hf

/-- The map between the canonical resaturations of the matched affine
analytifications. It has the same underlying map as `saturatedHom`. -/
def affineQuotientStrongModel :
    ofSaturation (saturated K Q).presentation ⟶ ofSaturation (saturated K P).presentation :=
  (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map (saturatedHom K P Q f)

private theorem exists_radius_chart_containing_compact {S : Set (Space K P)}
    (hS : IsCompact S) : ∃ m, S ⊆ range (chart K P m) := by
  let : Nonempty (presentation K P).atlas.Index := ⟨representative K P 0⟩
  have hnet := (presentation K P).atlas.isNet_chartFamily.1
  obtain ⟨i, hi⟩ := hnet.exists_subset_of_isCompact (atlas_hasDirectedCharts K P) hS
  exact ⟨i.val, hi⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem strongHom_matched_pullback_isAdmissibleEpi (m : ℕ)
    (h : (strongHom K P Q f).baseMap '' range ((presentation K Q).atlas.chart
      (representative K Q m)) ⊆ range ((presentation K P).atlas.chart (representative K P m))) :
    ((strongHom K P Q f).pullback (representative K Q m)
      (representative K P m) h).IsAdmissibleEpi := by
  let i : (presentation K Q).atlas.Index := representative K Q m
  let j : (presentation K P).atlas.Index := representative K P m
  let eP := representativeEquiv K P m
  let eQ := representativeEquiv K Q m
  let q := quotientRadiusMap K P f hf m
  have hMap : (strongHom K P Q f).pullback i j h =
      eQ.symm.toBoundedAlgHom.comp (q.comp eP.toBoundedAlgHom) := by
    apply hom_ext_coordinate
    intro t
    change (strongHom K P Q f).pullback i j h (coordinate K (algebra K P j.val) t) =
      eQ.symm (q (eP (coordinate K (algebra K P j.val) t)))
    refine (strongHom_pullback_coordinate P Q f i j h t).trans ?_
    apply eQ.injective
    let a := P.map (MvPolynomial.X t)
    have hP : eP (coordinate K (algebra K P j.val) t) =
        PolynomialLocus.algebraMap P (polyradius K P.arity m) a :=
      (congrArg eP (coordinate_eq_algebraMap P j.val t)).trans
        (equalRangeEquiv_algebraMap K P (range_representative K P m) a)
    have hq := quotientRadiusMap_algebraMap K P f hf m a
    have hQ := equalRangeEquiv_algebraMap K Q (range_representative K Q m) (f a)
    exact (hQ.trans (hq.symm.trans (congrArg q hP).symm)).trans
      (eQ.apply_symm_apply _).symm
  change ((strongHom K P Q f).pullback i j h).IsAdmissibleEpi
  rw [hMap]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _ (BoundedAlgHom.IsAdmissibleEpi.comp _ _
    eP.isAdmissibleEpi (quotientRadiusMap_isAdmissibleEpi K P f hf m)) eQ.symm.isAdmissibleEpi

set_option backward.isDefEq.respectTransparency false in
private theorem has_resaturated_quotient_charts (m : ℕ) :
    let X := saturated K Q
    let Y := saturated K P
    let g := affineQuotientStrongModel K P f hf
    ∃ (i : X.presentation.atlas.saturatedAtlas.Index)
      (j : Y.presentation.atlas.saturatedAtlas.Index)
      (hij : g.baseMap '' range (X.presentation.atlas.saturatedAtlas.chart i) ⊆
        range (Y.presentation.atlas.saturatedAtlas.chart j)),
      range (Y.presentation.atlas.saturatedAtlas.chart j) = range (chart K P m) ∧
      range (X.presentation.atlas.saturatedAtlas.chart i) = g.baseMap ⁻¹' range (chart K P m) ∧
      (g.pullback i j hij).IsAdmissibleEpi := by
  let X := saturated K Q
  let Y := saturated K P
  let g := affineQuotientStrongModel K P f hf
  let a := (presentation K Q).atlas
  let b := (presentation K P).atlas
  let i : a.Index := representative K Q m
  let j : b.Index := representative K P m
  let I : X.presentation.atlas.Index := a.originalSaturatedIndex i
  let J : Y.presentation.atlas.Index := b.originalSaturatedIndex j
  let I' := X.presentation.atlas.originalSaturatedIndex I
  let J' := Y.presentation.atlas.originalSaturatedIndex J
  have hI : range (X.presentation.atlas.chart I) = range (chart K Q m) :=
    (a.saturatedAtlas_original_range i).trans (range_representative K Q m)
  have hJ : range (Y.presentation.atlas.chart J) = range (chart K P m) :=
    (b.saturatedAtlas_original_range j).trans (range_representative K P m)
  have hII : range (X.presentation.atlas.saturatedAtlas.chart I') = range (chart K Q m) :=
    (X.presentation.atlas.saturatedAtlas_original_range I).trans hI
  have hJJ : range (Y.presentation.atlas.saturatedAtlas.chart J') = range (chart K P m) :=
    (Y.presentation.atlas.saturatedAtlas_original_range J).trans hJ
  have hpre := preimage_range_chart_quotient K P f hf m
  have h : (strongHom K P Q f).baseMap '' range (a.chart i) ⊆ range (b.chart j) := by
    change (baseMap K P Q f) '' range (chart K Q i.val) ⊆ range (chart K P j.val)
    rw [range_representative, range_representative, ← hpre]
    exact image_preimage_subset _ _
  let F : X ⟶ Y := saturatedHom K P Q f
  have hF : F.baseMap '' range (X.presentation.atlas.chart I) ⊆
      range (Y.presentation.atlas.chart J) :=
    (strongHom K P Q f).saturationExtension_original_admissible i j h
  have hG : g.baseMap '' range (X.presentation.atlas.saturatedAtlas.chart I') ⊆
      range (Y.presentation.atlas.saturatedAtlas.chart J') := by
    rw [hII, hJJ]
    change (baseMap K P Q f) '' range (chart K Q m) ⊆ range (chart K P m)
    rw [← hpre]
    exact image_preimage_subset _ _
  refine ⟨I', J', hG, hJJ, hII.trans hpre.symm, ?_⟩
  have hFadm : (F.pullback I J hF).IsAdmissibleEpi :=
    isAdmissibleEpi_of_heq (b.saturatedAtlas_original_algebra j)
      (a.saturatedAtlas_original_algebra i)
      ((strongHom K P Q f).saturationExtension_pullback_original
        (strongHom_hasCoherentPullbacks K P Q f) i j h)
      (strongHom_matched_pullback_isAdmissibleEpi K P f hf m h)
  exact isAdmissibleEpi_of_heq (Y.presentation.atlas.saturatedAtlas_original_algebra J)
    (X.presentation.atlas.saturatedAtlas_original_algebra I)
    (F.saturationExtension_pullback_original
      (F.hasCoherentPullbacks_of_saturated X.hasAllLocalDomains) I J hF) hFadm

set_option backward.isDefEq.respectTransparency false in
/-- The matched affine quotient map is a closed immersion between the
constructed resaturations. -/
theorem affineQuotientStrongModel_isClosedImmersion :
    (affineQuotientStrongModel K P f hf).IsClosedImmersion := by
  let X := saturated K Q
  let Y := saturated K P
  let g := affineQuotientStrongModel K P f hf
  intro W
  have hW : IsCompact W.locus := by
    rw [← W.range_chart]
    exact isCompact_range W.chart.continuous
  obtain ⟨m, hm⟩ := exists_radius_chart_containing_compact K P hW
  obtain ⟨i, j, hij, hj, hi, hq⟩ := has_resaturated_quotient_charts K P f hf m
  have hWj : W.locus ⊆ range (Y.presentation.atlas.saturatedAtlas.chart j) := hm.trans hj.symm.subset
  let V := g.recognizedPullback W i j hWj hij
  have hV := g.recognizedPullback_locus W i j hWj hij
  have hVW := g.recognizedPullback_admissible W i j hWj hij
  have hVi : V.locus ⊆ range (X.presentation.atlas.saturatedAtlas.chart i) :=
    hV.subset.trans inter_subset_left
  have hpre : g.baseMap ⁻¹' W.locus ⊆ range (X.presentation.atlas.saturatedAtlas.chart i) :=
    (Set.preimage_mono hm).trans hi.symm.subset
  refine ⟨V, hVW, hV.trans (inter_eq_right.mpr hpre), ?_⟩
  rw [g.fullRecognitionPairs_pullback_eq_pushout V W i j hVi hWj hij hVW hV]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    (AffinoidPushout.rightMap_isAdmissibleEpi _ _ hq)
    (g.fullRecognitionPullbackEquiv V W i j hVi hWj hij hV).isAdmissibleEpi

include hf in
set_option backward.isDefEq.respectTransparency false in
/-- A surjective affine algebra map induces a closed immersion of the
localized polynomial-locus analytifications for any presentations. -/
theorem closedImmersion_localizedHom_of_surjective (R : FinitePolynomialPresentation K B) :
    closedImmersion (localizedHom K P R f) := by
  let X := saturated K Q
  let Y := saturated K P
  let g := affineQuotientStrongModel K P f hf
  have heq : g ≫ Y.saturationIso.hom = X.saturationIso.hom ≫ saturatedHom K P Q f := by
    change ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map
      (saturatedHom K P Q f)) ≫ Y.saturationIso.hom = _
    rw [saturationExtension_eq_conjugate]
    change ((X.saturationIso.hom ≫ saturatedHom K P Q f) ≫ Y.saturationIso.inv) ≫
      Y.saturationIso.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hclosed : closedImmersion (localizedHom K P Q f) := by
    refine ⟨X.presentation, Y.presentation, g, affineQuotientStrongModel_isClosedImmersion K P f hf,
      ⟨Arrow.isoMk (localizationFunctor.mapIso X.saturationIso)
        (localizationFunctor.mapIso Y.saturationIso) ?_⟩⟩
    change localizationFunctor.map X.saturationIso.hom ≫
      localizationFunctor.map (saturatedHom K P Q f) =
      localizationFunctor.map g ≫ localizationFunctor.map Y.saturationIso.hom
    rw [← Functor.map_comp, ← Functor.map_comp, heq]
  let e := localizedHom K Q R (AlgHom.id K B)
  let : IsIso e :=
    (affineAnalytificationLocalizedFunctoriality K B B B Q R Q Q
      (AlgHom.id K B) (AlgHom.id K B)).2.2.2.2
  have hc : e ≫ localizedHom K P Q f = localizedHom K P R f := by
    rw [← (affineAnalytificationLocalizedFunctoriality K A B B P P Q R f
      (AlgHom.id K B)).2.2.2.1, AlgHom.id_comp]
  rw [← hc]
  exact MorphismProperty.RespectsIso.precomp closedImmersion e _ hclosed

end Langlands.Analytic.AffineAnalytification
