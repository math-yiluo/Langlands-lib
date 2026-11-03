import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Normalizers of subgroup intersections inside a monic ambient subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {C H G : GroupScheme S}

/-- A point normalizing both subgroup functors normalizes their intersection. -/
theorem inf_normalizer_le_normalizer_inf (F K : SubgroupFunctor G) :
    F.normalizer ⊓ K.normalizer ≤ (F ⊓ K).normalizer := by
  intro U g hg V a x hx
  have hF := hg.1 V a x hx.1
  have hK := hg.2 V a x hx.2
  exact ⟨⟨hF.1, hK.1⟩, ⟨hF.2, hK.2⟩⟩

/-- A point whose image normalizes a subgroup functor normalizes its preimage. -/
theorem comap_normalizer_le (j : H ⟶ G) (F : SubgroupFunctor G) :
    F.normalizer.comap j ≤ (F.comap j).normalizer := by
  intro U g hg V a x hx
  change g ≫ j.hom.hom ∈ F.normalizer.carrier U at hg
  have h := hg V a (x ≫ j.hom.hom) hx
  constructor
  · rw [mem_comap, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    simpa only [Category.assoc] using h.1
  · rw [mem_comap, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    simpa only [Category.assoc] using h.2

/-- The canonical inclusion from the preimage of an all-test normalizer into the
all-test normalizer of the preimage, evaluated on a test scheme. -/
def normalizerComapHom (j : H ⟶ G) (F : SubgroupFunctor G) (U : Over S) :
    (F.normalizer.comap j).carrier U →* (F.comap j).normalizer.carrier U :=
  Subgroup.inclusion (comap_normalizer_le j F U)

/-- An intersection equality after a monic inclusion identifies the internal
subgroup with the preimage of the other intersectand. -/
theorem range_eq_comap_of_range_comp_eq_inf
    (c : C ⟶ H) (j : H ⟶ G) [Mono j.hom.hom] (F : SubgroupFunctor G)
    (hrange : range (c ≫ j) = range j ⊓ F) :
    range c = F.comap j := by
  apply ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_range, mem_comap]
  constructor
  · rintro ⟨y, rfl⟩
    have h : (y ≫ c.hom.hom) ≫ j.hom.hom ∈ (range (c ≫ j)).carrier U := by
      apply mem_range.mpr
      refine ⟨y, ?_⟩
      rw [Grp.comp_hom_hom, Category.assoc]
    rw [hrange] at h
    exact h.2
  · intro hx
    have h : x ≫ j.hom.hom ∈ (range (c ≫ j)).carrier U := by
      rw [hrange]
      exact ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨y, hy⟩ := mem_range.mp h
    refine ⟨y, (cancel_mono j.hom.hom).mp ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy

/-- A normalizing point lifts to a normalizing point of an internal subgroup
whose ambient range is the actual intersection. Membership here is tested after
every refinement of the test scheme. -/
theorem mem_normalizer_of_range_comp_eq_inf
    (c : C ⟶ H) (j : H ⟶ G) [Mono j.hom.hom] (F : SubgroupFunctor G)
    (hrange : range (c ≫ j) = range j ⊓ F)
    {U : Over S} {x : U ⟶ H.X}
    (hx : x ≫ j.hom.hom ∈ F.normalizer.carrier U) :
    x ∈ (range c).normalizer.carrier U := by
  rw [range_eq_comap_of_range_comp_eq_inf c j F hrange]
  exact comap_normalizer_le j F U hx

/-- The same intersection argument for the abstract normalizer of the points on
one test scheme. It needs no passage from rational points to all test schemes. -/
theorem mem_pointNormalizer_of_range_comp_eq_inf
    (c : C ⟶ H) (j : H ⟶ G) [Mono j.hom.hom] (F : SubgroupFunctor G)
    (hrange : range (c ≫ j) = range j ⊓ F)
    {U : Over S} {x : U ⟶ H.X}
    (hx : x ≫ j.hom.hom ∈ Subgroup.normalizer (F.carrier U : Set (U ⟶ G.X))) :
    x ∈ Subgroup.normalizer ((range c).carrier U : Set (U ⟶ H.X)) := by
  rw [range_eq_comap_of_range_comp_eq_inf c j F hrange]
  exact Subgroup.le_normalizer_comap ((yonedaGrp.map j).app (op U)).hom hx

end Langlands.GroupScheme.SubgroupFunctor
