import Langlands.Geometry.Analytic.DirectedAtlasDomainCategory
import Langlands.Geometry.Analytic.AtlasAffinoidDomainLocalization

/-! # Localizing directed represented domains at an original atlas chart -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.DirectedDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (hd : a.HasDirectedCharts)

/-- The original chart is retained as the actual whole domain over its own
algebra, rather than replaced by an unspecified representative. -/
def originalChart (i : a.Index) : DirectedDomain a hd :=
  ⟨i, Domain.whole K (a.algebra i)⟩

@[simp]
theorem originalChart_locus (i : a.Index) :
    (originalChart a hd i).locus = Set.range (a.chart i) :=
  Set.image_univ

/-- The bounded structural map is the actual inclusion into the whole chart. -/
def toOriginalChart (i : a.Index) (U : Domain K (a.algebra i)) :
    (sameChartFunctor a hd i).obj U ⟶ originalChart a hd i :=
  (sameChartFunctor a hd i).map
    (show U ⟶ Domain.whole K (a.algebra i) from
      { restriction := U.baseMap, comp_baseMap := rfl })

@[simp]
theorem toOriginalChart_restriction (i : a.Index) (U : Domain K (a.algebra i)) :
    (toOriginalChart a hd i U).restriction = U.baseMap := rfl

/-- An actual global-domain arrow to an original chart makes its bounded map
a full domain representation over that chart. The proof uses a common original
upper chart and the already constructed original-chart restriction theorem. -/
theorem represents_toOriginalChart (i : a.Index) (U : DirectedDomain a hd)
    (f : U ⟶ originalChart a hd i) :
    Represents K f.restriction (a.chart i ⁻¹' U.locus) := by
  obtain ⟨q, hUq, hiq⟩ := hd U.index i
  let V := a.extendDomain U.index q hUq U.domain
  let g : V ⟶ a.restrictionDomain i q hiq :=
    { restriction := f.restriction
      comp_baseMap := by
        change f.restriction.comp (a.restriction i q hiq) =
          U.domain.baseMap.comp (a.restriction U.index q hUq)
        have h := f.comp_baseMap q hUq hiq
        change f.restriction.comp
            ((BoundedAlgHom.id K (a.algebra i)).comp (a.restriction i q hiq)) =
          U.domain.baseMap.comp (a.restriction U.index q hUq) at h
        simpa only [BoundedAlgHom.id_comp] using h }
  have hrep := a.represents_domainRestriction i q hiq V g
  have hlocus :
      (a.restrictionDomain i q hiq).spectrumMap ⁻¹' V.locus =
        a.chart i ⁻¹' U.locus := by
    ext x
    change (a.restrictionDomain i q hiq).spectrumMap x ∈ V.locus ↔
      a.chart i x ∈ U.locus
    have himage : a.chart q '' V.locus = U.locus :=
      a.chart_image_extendDomain_locus U.index q hUq U.domain
    rw [← himage]
    constructor
    · intro hx
      exact ⟨_, hx, a.restriction_chart i q hiq x⟩
    · rintro ⟨y, hy, he⟩
      have hyx : y = (a.restrictionDomain i q hiq).spectrumMap x :=
        (a.isEmbedding_chart q).injective
          (he.trans (a.restriction_chart i q hiq x).symm)
      exact hyx ▸ hy
  rw [hlocus] at hrep
  exact hrep

/-- Restrict the represented domain to a containing original chart. The actual
quotient algebra and the actual arrow's bounded map are retained literally. -/
def restrictToOriginalChart (i : a.Index) (U : DirectedDomain a hd)
    (f : U ⟶ originalChart a hd i) : Domain K (a.algebra i) where
  algebra := U.algebra
  baseMap := f.restriction
  locus := a.chart i ⁻¹' U.locus
  represents := represents_toOriginalChart a hd i U f

@[simp]
theorem restrictToOriginalChart_algebra (i : a.Index) (U : DirectedDomain a hd)
    (f : U ⟶ originalChart a hd i) :
    (restrictToOriginalChart a hd i U f).algebra = U.algebra := rfl

@[simp]
theorem restrictToOriginalChart_baseMap (i : a.Index) (U : DirectedDomain a hd)
    (f : U ⟶ originalChart a hd i) :
    (restrictToOriginalChart a hd i U f).baseMap = f.restriction := rfl

@[simp]
theorem restrictToOriginalChart_locus (i : a.Index) (U : DirectedDomain a hd)
    (f : U ⟶ originalChart a hd i) :
    (restrictToOriginalChart a hd i U f).locus = a.chart i ⁻¹' U.locus := rfl

/-- The new full representation gives exactly the original ambient locus. -/
theorem chart_image_restrictToOriginalChart_locus (i : a.Index)
    (U : DirectedDomain a hd) (f : U ⟶ originalChart a hd i) :
    a.chart i '' (restrictToOriginalChart a hd i U f).locus = U.locus := by
  change a.chart i '' (a.chart i ⁻¹' U.locus) = U.locus
  apply Set.image_preimage_eq_of_subset
  simpa only [originalChart_locus] using f.subset

/-- Fixed-chart full domains, equipped with their actual bounded structural
inclusion into the original chart. -/
def sameChartOverFunctor (i : a.Index) :
    Domain K (a.algebra i) ⥤ Over (originalChart a hd i) where
  obj U := Over.mk (toOriginalChart a hd i U)
  map {U V} f := Over.homMk ((sameChartFunctor a hd i).map f) (by
    apply Inclusion.ext
    exact f.comp_baseMap)
  map_id _ := by apply Over.OverMorphism.ext; apply Inclusion.ext; rfl
  map_comp _ _ := by apply Over.OverMorphism.ext; apply Inclusion.ext; rfl

/-- A commuting triangle over the original chart is the entire bounded base
map equation for its restricted full-domain representations. -/
def restrictOriginalChartFunctor (i : a.Index) :
    Over (originalChart a hd i) ⥤ Domain K (a.algebra i) where
  obj U := restrictToOriginalChart a hd i U.left U.hom
  map f := ⟨f.left.restriction, congrArg Inclusion.restriction f.w⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp]
theorem sameChartOverFunctor_map_restriction (i : a.Index)
    {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    ((sameChartOverFunctor a hd i).map f).left.restriction = f.restriction := rfl

@[simp]
theorem restrictOriginalChartFunctor_map_restriction (i : a.Index)
    {U V : Over (originalChart a hd i)} (f : U ⟶ V) :
    ((restrictOriginalChartFunctor a hd i).map f).restriction =
      f.left.restriction := rfl

/-- Restriction of a fixed-chart representation recovers it through bounded
identities on its actual quotient algebra. -/
def restrictSameChartIso (i : a.Index) (U : Domain K (a.algebra i)) :
    (restrictOriginalChartFunctor a hd i).obj ((sameChartOverFunctor a hd i).obj U) ≅
      U where
  hom := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

/-- The restricted representation is canonically the original directed-domain
object. Both arrows are proved below to have the identity bounded map. -/
def sameChartRestrictIso (i : a.Index) (U : DirectedDomain a hd)
    (f : U ⟶ originalChart a hd i) :
    (sameChartFunctor a hd i).obj (restrictToOriginalChart a hd i U f) ≅ U :=
  isoOfLocusEq _ _ (chart_image_restrictToOriginalChart_locus a hd i U f)

/-- The same actual algebra is being compared, so the identity is over each
common original upper chart by the original arrow's stored equation. -/
theorem sameChartRestrictIso_hom_restriction (i : a.Index)
    (U : DirectedDomain a hd) (f : U ⟶ originalChart a hd i) :
    (sameChartRestrictIso a hd i U f).hom.restriction =
      BoundedAlgHom.id K U.algebra := by
  obtain ⟨q, hUq, hiq⟩ := hd U.index i
  symm
  apply a.eq_directedDomainRestriction_of_over_base hd i U.index
    (restrictToOriginalChart a hd i U f) U.domain
    (sameChartRestrictIso a hd i U f).hom.subset q hiq hUq
  change U.domain.baseMap.comp (a.restriction U.index q hUq) =
    f.restriction.comp (a.restriction i q hiq)
  have h := f.comp_baseMap q hUq hiq
  change f.restriction.comp
      ((BoundedAlgHom.id K (a.algebra i)).comp (a.restriction i q hiq)) =
    U.domain.baseMap.comp (a.restriction U.index q hUq) at h
  simpa only [BoundedAlgHom.id_comp] using h.symm

theorem sameChartRestrictIso_inv_restriction (i : a.Index)
    (U : DirectedDomain a hd) (f : U ⟶ originalChart a hd i) :
    (sameChartRestrictIso a hd i U f).inv.restriction =
      BoundedAlgHom.id K U.algebra := by
  obtain ⟨q, hUq, hiq⟩ := hd U.index i
  symm
  apply a.eq_directedDomainRestriction_of_over_base hd U.index i
    U.domain (restrictToOriginalChart a hd i U f)
    (sameChartRestrictIso a hd i U f).inv.subset q hUq hiq
  change f.restriction.comp (a.restriction i q hiq) =
    U.domain.baseMap.comp (a.restriction U.index q hUq)
  have h := f.comp_baseMap q hUq hiq
  change f.restriction.comp
      ((BoundedAlgHom.id K (a.algebra i)).comp (a.restriction i q hiq)) =
    U.domain.baseMap.comp (a.restriction U.index q hUq) at h
  simpa only [BoundedAlgHom.id_comp] using h

/-- Localizing the actual directed-domain category at an original chart
recovers its full affinoid-domain category, with constructed inverse functors. -/
def originalChartLocalizationEquivalence (i : a.Index) :
    Domain K (a.algebra i) ≌ Over (originalChart a hd i) where
  functor := sameChartOverFunctor a hd i
  inverse := restrictOriginalChartFunctor a hd i
  unitIso := NatIso.ofComponents (fun U => (restrictSameChartIso a hd i U).symm)
    (by intro U V f; apply Domain.Inclusion.ext; rfl)
  counitIso := NatIso.ofComponents (fun U =>
    Over.isoMk (sameChartRestrictIso a hd i U.left U.hom) (by
      apply Inclusion.ext
      rw [Inclusion.restriction_comp, sameChartRestrictIso_hom_restriction]
      rfl)) (by
        intro U V f
        apply Over.OverMorphism.ext
        apply Inclusion.ext
        change f.left.restriction.comp
            (sameChartRestrictIso a hd i V.left V.hom).hom.restriction =
          (sameChartRestrictIso a hd i U.left U.hom).hom.restriction.comp
            f.left.restriction
        simp only [sameChartRestrictIso_hom_restriction,
          BoundedAlgHom.comp_id]
        rfl)
  functor_unitIso_comp U := by
    apply Over.OverMorphism.ext
    apply Inclusion.ext
    change (BoundedAlgHom.id K U.algebra).comp
        (sameChartRestrictIso a hd i
          ((sameChartOverFunctor a hd i).obj U).left
          ((sameChartOverFunctor a hd i).obj U).hom).hom.restriction =
      BoundedAlgHom.id K U.algebra
    rw [sameChartRestrictIso_hom_restriction]
    rfl

/-- Forgetting the original-chart inclusion recovers the actual fixed-chart
embedding. -/
theorem sameChartOverFunctor_comp_forget (i : a.Index) :
    sameChartOverFunctor a hd i ⋙ Over.forget (originalChart a hd i) =
      sameChartFunctor a hd i := rfl

/-- The localization inverse retains all actual quotient algebras and bounded
maps, hence exactly their affinoid and spectrum realization functors. -/
theorem restrictOriginalChartFunctor_comp_toAffinoidSpace (i : a.Index) :
    restrictOriginalChartFunctor a hd i ⋙ Domain.toAffinoidSpace K (a.algebra i) =
      Over.forget (originalChart a hd i) ⋙ toAffinoidSpace a hd := rfl

theorem restrictOriginalChartFunctor_comp_toTopologicalSpace (i : a.Index) :
    restrictOriginalChartFunctor a hd i ⋙ Domain.toTopologicalSpace K (a.algebra i) =
      Over.forget (originalChart a hd i) ⋙ toTopologicalSpace a hd := rfl

end Langlands.Analytic.IndexedAffinoidAtlas.DirectedDomain
