import Langlands.Geometry.Analytic.SaturatedTopChartComparison
import Langlands.Geometry.Analytic.ChartDomainSpectralTests
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange

/-! # Pair charts of a pullback square and the patches they identify -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section ChartDomainStrong

variable {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- The complete strong map of chart domains underlying the restriction of a
localized arrow which maps one chart into another. -/
def chartDomainStrong (φ : X ⟶ Y) (i : (presentationOf X).presentation.atlas.Index)
    (j : (presentationOf Y).presentation.atlas.Index)
    (h : ∀ x ∈ ((presentationOf X).chartDomain i).carrier,
      localizedSpaceFunctor.map φ x ∈ ((presentationOf Y).chartDomain j).carrier) :
    (presentationOf X).domain ((presentationOf X).chartDomain i) ⟶
      (presentationOf Y).domain ((presentationOf Y).chartDomain j) :=
  (localizedTopTargetHomEquiv (chartDomainFullChart _ j)
    (range_chart_subset_chartDomainFullChart _ j)).symm (domainRestrict _ _ φ h)

theorem localizationFunctor_map_chartDomainStrong (φ : X ⟶ Y)
    (i : (presentationOf X).presentation.atlas.Index)
    (j : (presentationOf Y).presentation.atlas.Index)
    (h : ∀ x ∈ ((presentationOf X).chartDomain i).carrier,
      localizedSpaceFunctor.map φ x ∈ ((presentationOf Y).chartDomain j).carrier) :
    localizationFunctor.map (chartDomainStrong φ i j h) = domainRestrict _ _ φ h := by
  unfold chartDomainStrong
  simpa only [localizedTopTargetHomEquiv_apply] using
    (localizedTopTargetHomEquiv (A := (presentationOf X).domain ((presentationOf X).chartDomain i))
      (chartDomainFullChart _ j) (range_chart_subset_chartDomainFullChart _ j)).apply_symm_apply
      (domainRestrict _ _ φ h)

end ChartDomainStrong

/-- Charts of the two factors of a cospan which both map into one chart of
the base. -/
structure PairChartData {B U V : LocalizedCategory.{u, v, v} (K := K)}
    (f : U ⟶ B) (g : V ⟶ B) where
  /-- The chart of the first factor. -/
  left : (presentationOf U).presentation.atlas.Index
  /-- The chart of the second factor. -/
  right : (presentationOf V).presentation.atlas.Index
  /-- The common chart of the base. -/
  base : (presentationOf B).presentation.atlas.Index
  left_mapsTo : ∀ x ∈ ((presentationOf U).chartDomain left).carrier,
    localizedSpaceFunctor.map f x ∈ ((presentationOf B).chartDomain base).carrier
  right_mapsTo : ∀ x ∈ ((presentationOf V).chartDomain right).carrier,
    localizedSpaceFunctor.map g x ∈ ((presentationOf B).chartDomain base).carrier

namespace PairChartData

variable {B U V P : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ B} {g : V ⟶ B}
  (c : PairChartData f g)

/-- The chart domain of the first factor. -/
abbrev leftDomain : (presentationOf U).AnalyticDomain := (presentationOf U).chartDomain c.left

/-- The chart domain of the second factor. -/
abbrev rightDomain : (presentationOf V).AnalyticDomain := (presentationOf V).chartDomain c.right

/-- The chart domain of the base. -/
abbrev baseDomain : (presentationOf B).AnalyticDomain := (presentationOf B).chartDomain c.base

/-- The restriction of the first cospan arrow to the charts. -/
def leftMap : domainObj U c.leftDomain ⟶ domainObj B c.baseDomain :=
  domainRestrict _ _ f c.left_mapsTo

/-- The restriction of the second cospan arrow to the charts. -/
def rightMap : domainObj V c.rightDomain ⟶ domainObj B c.baseDomain :=
  domainRestrict _ _ g c.right_mapsTo

@[reassoc]
theorem leftMap_comp : c.leftMap ≫ domainι B c.baseDomain = domainι U c.leftDomain ≫ f :=
  domainRestrict_comp _ _ _ _

@[reassoc]
theorem rightMap_comp : c.rightMap ≫ domainι B c.baseDomain = domainι V c.rightDomain ≫ g :=
  domainRestrict_comp _ _ _ _

/-- The bounded algebra map of the first chart restriction on full charts. -/
abbrev leftTop : BoundedAlgHom K ((presentationOf B).presentation.atlas.algebra c.base)
    ((presentationOf U).presentation.atlas.algebra c.left) :=
  (chartDomainStrong f c.left c.base c.left_mapsTo).pullbackAtTop
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.base)
    (chartDomainFullChart _ c.left)

/-- The bounded algebra map of the second chart restriction on full charts. -/
abbrev rightTop : BoundedAlgHom K ((presentationOf B).presentation.atlas.algebra c.base)
    ((presentationOf V).presentation.atlas.algebra c.right) :=
  (chartDomainStrong g c.right c.base c.right_mapsTo).pullbackAtTop
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.base)
    (chartDomainFullChart _ c.right)

/-- The pushout algebra of the two chart algebras over the base chart algebra. -/
abbrev algebra : PresentedAffinoidAlgebra K := AffinoidPushout.algebra c.leftTop c.rightTop

section Object

variable [hc : Small.{v} (BanachSpectrum c.algebra)]
include hc

/-- The pair chart: the small spectrum of the pushout algebra, presented as a
greatest-chart pullback of the two chart domains. -/
def obj : SaturatedAtlasPresentation.{u, v, v} K :=
  @greatestChartPullback _ _ _ _ _ _ _ (chartDomainStrong f c.left c.base c.left_mapsTo)
    (chartDomainStrong g c.right c.base c.right_mapsTo)
    (chartDomainFullChart _ c.left) (chartDomainFullChart _ c.right)
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.base) hc

/-- The first projection of the pair chart. -/
def fst : localizationFunctor.obj c.obj ⟶ domainObj U c.leftDomain :=
  localizationFunctor.map (@greatestChartPullbackFst _ _ _ _ _ _ _
    (chartDomainStrong f c.left c.base c.left_mapsTo)
    (chartDomainStrong g c.right c.base c.right_mapsTo)
    (chartDomainFullChart _ c.left) (chartDomainFullChart _ c.right)
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.left)
    (range_chart_subset_chartDomainFullChart _ c.base) hc)

/-- The second projection of the pair chart. -/
def snd : localizationFunctor.obj c.obj ⟶ domainObj V c.rightDomain :=
  localizationFunctor.map (@greatestChartPullbackSnd _ _ _ _ _ _ _
    (chartDomainStrong f c.left c.base c.left_mapsTo)
    (chartDomainStrong g c.right c.base c.right_mapsTo)
    (chartDomainFullChart _ c.left) (chartDomainFullChart _ c.right)
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.right)
    (range_chart_subset_chartDomainFullChart _ c.base) hc)

/-- The pair chart is a pullback of the two chart restrictions. -/
theorem isPullback : IsPullback c.fst c.snd c.leftMap c.rightMap := by
  have h := @greatestChartPullback_localized_isPullback _ _ _ _ _ _ _
    (chartDomainStrong f c.left c.base c.left_mapsTo)
    (chartDomainStrong g c.right c.base c.right_mapsTo)
    (chartDomainFullChart _ c.left) (chartDomainFullChart _ c.right)
    (chartDomainFullChart _ c.base) (range_chart_subset_chartDomainFullChart _ c.left)
    (range_chart_subset_chartDomainFullChart _ c.right)
    (range_chart_subset_chartDomainFullChart _ c.base) hc
  rw [localizationFunctor_map_chartDomainStrong, localizationFunctor_map_chartDomainStrong] at h
  exact h

end Object

variable {p : P ⟶ U} {q : P ⟶ V}

/-- The patch of the pullback lying over both charts. -/
def patch (p : P ⟶ U) (q : P ⟶ V) : (presentationOf P).AnalyticDomain :=
  domainPreimage p c.leftDomain ⊓ domainPreimage q c.rightDomain

theorem mem_patch_iff (x : localizedSpaceFunctor.obj P) :
    x ∈ c.patch p q ↔ localizedSpaceFunctor.map p x ∈ c.leftDomain ∧
      localizedSpaceFunctor.map q x ∈ c.rightDomain := Iff.rfl

theorem patch_left_mapsTo : ∀ x ∈ (c.patch p q).carrier,
    localizedSpaceFunctor.map p x ∈ c.leftDomain.carrier := fun _ hx => hx.1

theorem patch_right_mapsTo : ∀ x ∈ (c.patch p q).carrier,
    localizedSpaceFunctor.map q x ∈ c.rightDomain.carrier := fun _ hx => hx.2

/-- The first projection restricted to the patch. -/
def patchFst (p : P ⟶ U) (q : P ⟶ V) : domainObj P (c.patch p q) ⟶ domainObj U c.leftDomain :=
  domainRestrict _ _ p c.patch_left_mapsTo

/-- The second projection restricted to the patch. -/
def patchSnd (p : P ⟶ U) (q : P ⟶ V) : domainObj P (c.patch p q) ⟶ domainObj V c.rightDomain :=
  domainRestrict _ _ q c.patch_right_mapsTo

@[reassoc]
theorem patchFst_comp : c.patchFst p q ≫ domainι U c.leftDomain = domainι P (c.patch p q) ≫ p :=
  domainRestrict_comp _ _ _ _

@[reassoc]
theorem patchSnd_comp : c.patchSnd p q ≫ domainι V c.rightDomain = domainι P (c.patch p q) ≫ q :=
  domainRestrict_comp _ _ _ _

variable (hP : IsPullback p q f g)
include hP

theorem patch_condition : c.patchFst p q ≫ c.leftMap = c.patchSnd p q ≫ c.rightMap := by
  apply (cancel_mono (domainι B c.baseDomain)).1
  rw [Category.assoc, Category.assoc, c.leftMap_comp, c.rightMap_comp, c.patchFst_comp_assoc,
    c.patchSnd_comp_assoc, hP.w]

section Object

variable [hc : Small.{v} (BanachSpectrum c.algebra)]
include hc

omit hP in
theorem pair_condition : (c.fst ≫ domainι U c.leftDomain) ≫ f =
    (c.snd ≫ domainι V c.rightDomain) ≫ g := by
  rw [Category.assoc, Category.assoc, ← c.leftMap_comp, ← c.rightMap_comp,
    ← Category.assoc, c.isPullback.w, Category.assoc]

/-- The canonical arrow from the pair chart to the pullback. -/
def toP : localizationFunctor.obj c.obj ⟶ P :=
  hP.lift (c.fst ≫ domainι U c.leftDomain) (c.snd ≫ domainι V c.rightDomain) c.pair_condition

@[reassoc (attr := simp)]
theorem toP_fst : c.toP hP ≫ p = c.fst ≫ domainι U c.leftDomain := hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toP_snd : c.toP hP ≫ q = c.snd ≫ domainι V c.rightDomain := hP.lift_snd _ _ _

theorem toP_mem_patch (x : localizedSpaceFunctor.obj (localizationFunctor.obj c.obj)) :
    localizedSpaceFunctor.map (c.toP hP) x ∈ (c.patch p q).carrier := by
  constructor
  · change localizedSpaceFunctor.map p (localizedSpaceFunctor.map (c.toP hP) x) ∈ c.leftDomain
    rw [← TopCat.comp_app, ← Functor.map_comp, c.toP_fst hP, Functor.map_comp, TopCat.comp_app,
      domainι_apply]
    exact Subtype.property _
  · change localizedSpaceFunctor.map q (localizedSpaceFunctor.map (c.toP hP) x) ∈ c.rightDomain
    rw [← TopCat.comp_app, ← Functor.map_comp, c.toP_snd hP, Functor.map_comp, TopCat.comp_app,
      domainι_apply]
    exact Subtype.property _

/-- The canonical arrow from the pair chart to the patch. -/
def toPatch : localizationFunctor.obj c.obj ⟶ domainObj P (c.patch p q) :=
  domainLift _ (c.toP hP) (c.toP_mem_patch hP)

@[reassoc (attr := simp)]
theorem toPatch_comp : c.toPatch hP ≫ domainι P (c.patch p q) = c.toP hP :=
  domainLift_comp _ _ _

/-- The canonical arrow from the patch to the pair chart. -/
def fromPatch : domainObj P (c.patch p q) ⟶ localizationFunctor.obj c.obj :=
  c.isPullback.lift (c.patchFst p q) (c.patchSnd p q) (c.patch_condition hP)

@[reassoc (attr := simp)]
theorem fromPatch_fst : c.fromPatch hP ≫ c.fst = c.patchFst p q := c.isPullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fromPatch_snd : c.fromPatch hP ≫ c.snd = c.patchSnd p q := c.isPullback.lift_snd _ _ _

theorem toPatch_fromPatch : c.toPatch hP ≫ c.fromPatch hP = 𝟙 _ := by
  apply c.isPullback.hom_ext
  · apply (cancel_mono (domainι U c.leftDomain)).1
    simp only [Category.assoc, c.fromPatch_fst_assoc, c.patchFst_comp, c.toPatch_comp_assoc,
      c.toP_fst, Category.id_comp]
  · apply (cancel_mono (domainι V c.rightDomain)).1
    simp only [Category.assoc, c.fromPatch_snd_assoc, c.patchSnd_comp, c.toPatch_comp_assoc,
      c.toP_snd, Category.id_comp]

theorem fromPatch_toPatch : c.fromPatch hP ≫ c.toPatch hP = 𝟙 _ := by
  apply (cancel_mono (domainι P (c.patch p q))).1
  rw [Category.assoc, c.toPatch_comp, Category.id_comp]
  apply hP.hom_ext
  · rw [Category.assoc, c.toP_fst, c.fromPatch_fst_assoc, c.patchFst_comp]
  · rw [Category.assoc, c.toP_snd, c.fromPatch_snd_assoc, c.patchSnd_comp]

/-- The pair chart is isomorphic to the patch of the pullback over its two charts. -/
@[simps]
def patchIso : localizationFunctor.obj c.obj ≅ domainObj P (c.patch p q) where
  hom := c.toPatch hP
  inv := c.fromPatch hP
  hom_inv_id := c.toPatch_fromPatch hP
  inv_hom_id := c.fromPatch_toPatch hP

end Object

end PairChartData

end Langlands.Analytic.SaturatedAtlasPresentation
