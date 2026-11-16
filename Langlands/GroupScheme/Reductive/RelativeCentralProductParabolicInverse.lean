import Langlands.GroupScheme.Reductive.RelativeCentralProductParabolic
import Langlands.GroupScheme.Reductive.DerivedCorrespondenceInjectivity
import Langlands.GroupScheme.RelativeLevi.DynamicProof
import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleLocality
import Langlands.GroupScheme.SubgroupFunctor.CoverMatching

/-! # Local relative parabolic extensions in a central product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- Inverse images of subgroup functors commute with arbitrary base change. -/
theorem baseChange_comap {S S' : Scheme.{u}} {D G : GroupScheme S}
    (b : S' ⟶ S) (d : D ⟶ G) (F : SubgroupFunctor G) :
    (F.comap d).baseChange b = (F.baseChange b).comap ((GroupScheme.baseChange b).map d) := by
  ext T x
  change (baseChangePointsEquiv b D T x ≫ d.hom.hom ∈ F.carrier _) ↔
    (baseChangePointsEquiv b G T (x ≫ ((GroupScheme.baseChange b).map d).hom.hom) ∈ F.carrier _)
  rw [baseChangePointsEquiv_comp]

end SubgroupFunctor

namespace CentralProductParabolic

variable {S : Scheme.{u}} {D G P' Z : GroupScheme S}

/-- An ambient relative parabolic whose inverse image is a prescribed subgroup. -/
structure RelativeExtension (d : D ⟶ G) (i' : P' ⟶ D) where
  group : GroupScheme S
  inclusion : group ⟶ G
  parabolic : IsRelativeParabolicSubgroup inclusion
  inverseImage : (SubgroupFunctor.range inclusion).comap d = SubgroupFunctor.range i'

namespace RelativeExtension

variable {d : D ⟶ G} {i' : P' ⟶ D}

/-- A cocharacter presenting the subgroup of a closed factor gives an ambient
relative parabolic extension over any base scheme. -/
def ofDynamic (hG : IsReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (i' : P' ⟶ D) (χ : (Gm S).toGrp ⟶ D)
    (hχ : SubgroupFunctor.range i' = Dynamic.parabolic χ) : RelativeExtension d i' := by
  apply Classical.choice
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFinitePresentation G.X.hom := inferInstance
  obtain ⟨P, i, _, _, hP⟩ := (dynamicBaseRepresentability S G (χ ≫ d)).1
  obtain ⟨U, iU, _, _, hU⟩ := (dynamicBaseRepresentability S G (χ ≫ d)).2.1
  obtain ⟨L, iL, _, _, hL⟩ := (dynamicBaseRepresentability S G (χ ≫ d)).2.2
  refine ⟨⟨P, i, (dynamicRelativeLevi S G P U L (χ ≫ d) i iU iL hG hP hU hL).1, ?_⟩⟩
  rw [hP.2, ← Dynamic.parabolic_eq_comap_of_isClosedSubgroup χ d hd, hχ]

/-- The defining inverse-image equality is exactly the all-test range of the
actual scheme-theoretic intersection. -/
theorem intersection_range (w : RelativeExtension d i') :
    SubgroupFunctor.range (subgroupIntersectionFst d w.inclusion) =
      SubgroupFunctor.range i' := by
  rw [range_subgroupIntersectionFst_eq_comap, w.inverseImage]

/-- Pull back an actual relative extension along any morphism of bases. -/
def baseChange (w : RelativeExtension d i') (hG : IsReductive G)
    {S' : Scheme.{u}} (b : S' ⟶ S) :
    RelativeExtension ((GroupScheme.baseChange b).map d) ((GroupScheme.baseChange b).map i') where
  group := (GroupScheme.baseChange b).obj w.group
  inclusion := (GroupScheme.baseChange b).map w.inclusion
  parabolic := w.parabolic.baseChange hG b
  inverseImage := by
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.baseChange_comap,
      w.inverseImage, SubgroupFunctor.range_baseChangeHom]

/-- Commuting isomorphisms of the ambient group, factor and prescribed subgroup
transport an extension. -/
def transport (w : RelativeExtension d i')
    {D₂ G₂ P₂ : GroupScheme S} {d₂ : D₂ ⟶ G₂} {i₂ : P₂ ⟶ D₂}
    (eD : D ≅ D₂) (eG : G ≅ G₂) (eP : P' ≅ P₂)
    (hd : d ≫ eG.hom = eD.hom ≫ d₂)
    (hi : i' ≫ eD.hom = eP.hom ≫ i₂) : RelativeExtension d₂ i₂ where
  group := w.group
  inclusion := w.inclusion ≫ eG.hom
  parabolic := w.parabolic.comp_iso eG
  inverseImage := by
    have hd' : d₂ ≫ eG.inv = eD.inv ≫ d := by
      rw [← Iso.cancel_iso_hom_left eD]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hi' : i₂ ≫ eD.inv = eP.inv ≫ i' := by
      rw [← Iso.cancel_iso_hom_left eP]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [SubgroupFunctor.range_comp_iso, ← SubgroupFunctor.comap_comp, hd',
      SubgroupFunctor.comap_comp, w.inverseImage,
      ← SubgroupFunctor.range_comp_iso i' eD, hi, SubgroupFunctor.range_iso_comp]

/-- A supplied central product isogeny makes an extension unique as an
all-test subgroup functor of the ambient group. -/
theorem range_unique (w v : RelativeExtension d i') (hG : IsReductive G)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _))) :
    SubgroupFunctor.range w.inclusion = SubgroupFunctor.range v.inclusion := by
  apply DerivedCorrespondence.parabolic_injective_of_isogenies d z hz
    (fun P i hi => ⟨relativeIntersectionFactor hG i hi z hz d,
      isCentralIsogeny_relativeIntersectionFactor hG i hi z hz d hprod,
      relativeIntersectionFactor_comp hG i hi z hz d⟩)
    w.group v.group w.inclusion v.inclusion w.parabolic v.parabolic
  exact w.intersection_range.trans v.intersection_range.symm

end RelativeExtension
end CentralProductParabolic
end Langlands.GroupScheme
