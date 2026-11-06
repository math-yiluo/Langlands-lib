import Langlands.Geometry.Analytic.SpecialChartCover
import Langlands.Geometry.Analytic.AtlasDomainCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainProduct
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushout
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutAdmissibility

/-! # Full-domain intersections between two members of a special cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a) (i j : Fin d.size)

theorem overlapPresentationMap_comp_leftMap :
    (d.overlapPresentationMap i j).comp
        (AffinoidCoproduct.leftMap K (a.algebra (d.index i)) (a.algebra (d.index j))) =
      d.leftRestriction i j :=
  AffinoidCoproduct.lift_comp_leftMap _ _ _ _ _ _

theorem overlapPresentationMap_comp_rightMap :
    (d.overlapPresentationMap i j).comp
        (AffinoidCoproduct.rightMap K (a.algebra (d.index i)) (a.algebra (d.index j))) =
      d.rightRestriction i j :=
  AffinoidCoproduct.lift_comp_rightMap _ _ _ _ _ _

theorem overlapPresentationMap_isAdmissibleEpi
    (h : (d.overlapTensorMap i j).IsAdmissibleEpi) :
    (d.overlapPresentationMap i j).IsAdmissibleEpi := by
  apply BoundedAlgHom.IsAdmissibleEpi.of_comp (d.overlapPresentationMap i j)
    (AffinoidCoproduct.fromCompletedTensor K
      (a.algebra (d.index i)) (a.algebra (d.index j)))
  rw [overlapPresentationMap_comp_fromCompletedTensor]
  exact h

theorem overlapProduct_left_chart (z : BanachSpectrum (a.algebra (d.overlap i j))) :
    a.chart (d.index i)
      (BanachSpectrum.comap
        (AffinoidCoproduct.leftMap K (a.algebra (d.index i))
          (a.algebra (d.index j))).toBoundedRingHom
        (BanachSpectrum.comap (d.overlapPresentationMap i j).toBoundedRingHom z)) =
      a.chart (d.overlap i j) z := by
  change a.chart (d.index i)
    (BanachSpectrum.comap
      ((d.overlapPresentationMap i j).comp
        (AffinoidCoproduct.leftMap K (a.algebra (d.index i))
          (a.algebra (d.index j)))).toBoundedRingHom z) = _
  rw [overlapPresentationMap_comp_leftMap]
  exact a.restriction_chart _ _ _ z

theorem overlapProduct_right_chart (z : BanachSpectrum (a.algebra (d.overlap i j))) :
    a.chart (d.index j)
      (BanachSpectrum.comap
        (AffinoidCoproduct.rightMap K (a.algebra (d.index i))
          (a.algebra (d.index j))).toBoundedRingHom
        (BanachSpectrum.comap (d.overlapPresentationMap i j).toBoundedRingHom z)) =
      a.chart (d.overlap i j) z := by
  change a.chart (d.index j)
    (BanachSpectrum.comap
      ((d.overlapPresentationMap i j).comp
        (AffinoidCoproduct.rightMap K (a.algebra (d.index i))
          (a.algebra (d.index j)))).toBoundedRingHom z) = _
  rw [overlapPresentationMap_comp_rightMap]
  exact a.restriction_chart _ _ _ z

variable (U : Domain K (a.algebra (d.index i))) (V : Domain K (a.algebra (d.index j)))

/-- Pull the full product domain back along the actual original overlap map. -/
def domainIntersection : LocalDomain a :=
  ⟨d.overlap i j, Domain.pullback (d.overlapPresentationMap i j) (U.product V)⟩

theorem domainIntersection_locus :
    (d.domainIntersection i j U V).locus =
      (a.chart (d.index i) '' U.locus) ∩ (a.chart (d.index j) '' V.locus) := by
  change a.chart (d.overlap i j) ''
    ((BanachSpectrum.comap (d.overlapPresentationMap i j).toBoundedRingHom) ⁻¹'
      (U.product V).locus) = _
  ext x
  constructor
  · rintro ⟨z, ⟨hzU, hzV⟩, rfl⟩
    exact ⟨⟨_, hzU, d.overlapProduct_left_chart i j z⟩,
      ⟨_, hzV, d.overlapProduct_right_chart i j z⟩⟩
  · rintro ⟨⟨u, hu, hux⟩, ⟨v, hv, hvx⟩⟩
    have hx : x ∈ Set.range (a.chart (d.overlap i j)) := by
      rw [d.overlap_range]
      exact ⟨⟨u, hux⟩, ⟨v, hvx⟩⟩
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, ⟨?_, ?_⟩, hz⟩
    · have heq := (a.isEmbedding_chart (d.index i)).injective
        ((d.overlapProduct_left_chart i j z).trans (hz.trans hux.symm))
      change _ ∈ U.locus
      exact heq.symm ▸ hu
    · have heq := (a.isEmbedding_chart (d.index j)).injective
        ((d.overlapProduct_right_chart i j z).trans (hz.trans hvx.symm))
      change _ ∈ V.locus
      exact heq.symm ▸ hv

def domainIntersectionLeftMap :
    BoundedAlgHom K U.algebra (d.domainIntersection i j U V).algebra :=
  (Domain.pullbackMap (d.overlapPresentationMap i j) (U.product V)).comp
    (U.productLeftMap V)

def domainIntersectionRightMap :
    BoundedAlgHom K V.algebra (d.domainIntersection i j U V).algebra :=
  (Domain.pullbackMap (d.overlapPresentationMap i j) (U.product V)).comp
    (U.productRightMap V)

theorem domainIntersectionLeftMap_comp_baseMap :
    (d.domainIntersectionLeftMap i j U V).comp U.baseMap =
      (d.domainIntersection i j U V).domain.baseMap.comp (d.leftRestriction i j) := by
  change ((Domain.pullbackMap _ _).comp (U.productLeftMap V)).comp U.baseMap = _
  rw [BoundedAlgHom.comp_assoc, Domain.productLeftMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
    BoundedAlgHom.comp_assoc, overlapPresentationMap_comp_leftMap]
  rfl

theorem domainIntersectionRightMap_comp_baseMap :
    (d.domainIntersectionRightMap i j U V).comp V.baseMap =
      (d.domainIntersection i j U V).domain.baseMap.comp (d.rightRestriction i j) := by
  change ((Domain.pullbackMap _ _).comp (U.productRightMap V)).comp V.baseMap = _
  rw [BoundedAlgHom.comp_assoc, Domain.productRightMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
    BoundedAlgHom.comp_assoc, overlapPresentationMap_comp_rightMap]
  rfl

/-- The inclusion is the canonical full-domain restriction, defined from
literal ambient containment. -/
def domainIntersectionLeft :
    d.domainIntersection i j U V ⟶ (⟨d.index i, U⟩ : LocalDomain a) :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [domainIntersection_locus]
    exact Set.inter_subset_left)

def domainIntersectionRight :
    d.domainIntersection i j U V ⟶ (⟨d.index j, V⟩ : LocalDomain a) :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [domainIntersection_locus]
    exact Set.inter_subset_right)

theorem domainIntersectionLeft_restriction :
    (d.domainIntersectionLeft i j U V).restriction =
      d.domainIntersectionLeftMap i j U V := by
  rw [LocalDomain.Inclusion.restriction_eq]
  symm
  apply a.eq_domainRestriction_of_over_base
  exact (d.domainIntersectionLeftMap_comp_baseMap i j U V).trans
    (a.domainChartRestriction_of_chartSubset (d.overlap i j) (d.index i)
      (d.domainIntersection i j U V).domain _ (d.overlap_subset_left i j)).symm

theorem domainIntersectionRight_restriction :
    (d.domainIntersectionRight i j U V).restriction =
      d.domainIntersectionRightMap i j U V := by
  rw [LocalDomain.Inclusion.restriction_eq]
  symm
  apply a.eq_domainRestriction_of_over_base
  exact (d.domainIntersectionRightMap_comp_baseMap i j U V).trans
    (a.domainChartRestriction_of_chartSubset (d.overlap i j) (d.index j)
      (d.domainIntersection i j U V).domain _ (d.overlap_subset_right i j)).symm

theorem domainIntersection_tensor_isAdmissibleEpi
    (h : (d.overlapTensorMap i j).IsAdmissibleEpi) :
    (CompletedTensorAlgebra.lift
      (d.domainIntersectionLeft i j U V).restriction
      (d.domainIntersectionRight i j U V).restriction).IsAdmissibleEpi := by
  rw [domainIntersectionLeft_restriction, domainIntersectionRight_restriction]
  let β := Domain.pullbackMap (d.overlapPresentationMap i j) (U.product V)
  have hβ : β.IsAdmissibleEpi :=
    AffinoidPushout.rightMap_isAdmissibleEpi _ _
      (d.overlapPresentationMap_isAdmissibleEpi i j h)
  have hp : (U.productCoproductMap V).IsAdmissibleEpi :=
    BoundedAlgHom.isAdmissibleEpi_of_bounded_section _ (U.productToCoproductMap V)
      (U.productCoproductMap_comp_productToCoproductMap V)
  have ht : (AffinoidCoproduct.fromCompletedTensor K U.algebra V.algebra).IsAdmissibleEpi :=
    BoundedAlgHom.isAdmissibleEpi_of_bounded_section _
      (AffinoidCoproduct.toCompletedTensor K U.algebra V.algebra)
      (AffinoidCoproduct.fromCompletedTensor_comp_toCompletedTensor K U.algebra V.algebra)
  have hmaps :
      AffinoidCoproduct.lift K (d.domainIntersection i j U V).algebra
          U.algebra V.algebra
          (d.domainIntersectionLeftMap i j U V) (d.domainIntersectionRightMap i j U V) =
        β.comp (U.productCoproductMap V) := by
    apply AffinoidCoproduct.hom_ext K _ U.algebra V.algebra
    · rw [AffinoidCoproduct.lift_comp_leftMap]
      exact (congrArg
        (fun γ : BoundedAlgHom K U.algebra (U.product V).algebra => β.comp γ)
        (U.productCoproductMap_comp_leftMap V)).symm
    · rw [AffinoidCoproduct.lift_comp_rightMap]
      exact (congrArg
        (fun γ : BoundedAlgHom K V.algebra (U.product V).algebra => β.comp γ)
        (U.productCoproductMap_comp_rightMap V)).symm
  rw [← AffinoidCoproduct.lift_comp_fromCompletedTensor, hmaps]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    ht (BoundedAlgHom.IsAdmissibleEpi.comp _ _ hp hβ)

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
