import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent
import Langlands.GroupScheme.CentralIsogeny.ProductIntersectionRestriction
import Langlands.GroupScheme.SubgroupFunctor.FpqcProductReconstruction
import Langlands.AbelianScheme.IsogenyInverse

/-! # Central-product factorizations of relative maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace RelativeDerivedTorus

variable {S : Scheme.{u}} {G D Z : GroupScheme S}
  (hG : IsReductive G) (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
  {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
  (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)

/-- Multiplication from the central factor and the full derived intersection,
factored through the specified relative maximal torus. -/
def intersectionFactor : Z ⊗ subgroupIntersection d t ⟶ T.toGrp := by
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  exact centralProductIntersectionFactor z hz d t
    (((isCentral_iff_range_le_center z).mp hz).trans
      (center_le_range_relativeMaximalTorus hG hT t ht hmax))

/-- The factor has the prescribed multiplication composite. -/
@[reassoc (attr := simp)]
theorem intersectionFactor_comp :
    intersectionFactor hG z hz d hT t ht hmax ≫ t =
      prodHom z (subgroupIntersectionHom d t) (hz.commute_values _) := by
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  unfold intersectionFactor
  exact centralProductIntersectionFactor_comp _ _ _ _ _

/-- A supplied global central-product isogeny restricts to the actual
relative maximal torus as a central isogeny. -/
theorem isCentralIsogeny_intersectionFactor
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _))) :
    IsCentralIsogeny (intersectionFactor hG z hz d hT t ht hmax) := by
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  unfold intersectionFactor
  exact isCentralIsogeny_centralProductIntersectionFactor z hz d hprod t _

end RelativeDerivedTorus

/-- Postcomposition preserves equality of all-test range functors. -/
theorem SubgroupFunctor.range_comp_eq_of_range_eq
    {S : Scheme.{u}} {A B D G : GroupScheme S}
    (a : A ⟶ D) (b : B ⟶ D) (d : D ⟶ G)
    (h : SubgroupFunctor.range a = SubgroupFunctor.range b) :
    SubgroupFunctor.range (a ≫ d) = SubgroupFunctor.range (b ≫ d) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ a.hom.hom ∈ (SubgroupFunctor.range b).carrier U := by
      rw [← h]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hy
    refine SubgroupFunctor.mem_range.mpr ⟨v, ?_⟩
    simp only [Grp.comp_hom_hom, ← Category.assoc, hv]
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ b.hom.hom ∈ (SubgroupFunctor.range a).carrier U := by
      rw [h]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hy
    refine SubgroupFunctor.mem_range.mpr ⟨v, ?_⟩
    simp only [Grp.comp_hom_hom, ← Category.assoc, hv]

namespace RelativeDerivedTorus

/-- Under the global central-product isogeny, relative maximal tori with the
same full intersection in the supplied derived subgroup have the same range. -/
theorem range_eq_of_intersections
    {S : Scheme.{u}} {G D Z : GroupScheme S}
    (hG : IsReductive G) (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    {T₁ T₂ : CommGroupScheme S}
    (t₁ : T₁.toGrp ⟶ G) (hT₁ : RelativeTorus.IsTorus T₁.toGrp)
    (ht₁ : IsClosedSubgroup t₁) (hmax₁ : IsFibrewiseMaximalTorus t₁)
    (t₂ : T₂.toGrp ⟶ G) (hT₂ : RelativeTorus.IsTorus T₂.toGrp)
    (ht₂ : IsClosedSubgroup t₂) (hmax₂ : IsFibrewiseMaximalTorus t₂)
    (hi : SubgroupFunctor.range (subgroupIntersectionFst d t₁) =
      SubgroupFunctor.range (subgroupIntersectionFst d t₂)) :
    SubgroupFunctor.range t₁ = SubgroupFunctor.range t₂ := by
  let : IsClosedImmersion t₁.hom.hom.left := ht₁
  let : Mono t₁.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion t₂.hom.hom.left := ht₂
  let : Mono t₂.hom.hom := Over.mono_of_mono_left _
  let e₁ := intersectionFactor hG z hz d hT₁ t₁ ht₁ hmax₁
  let e₂ := intersectionFactor hG z hz d hT₂ t₂ ht₂ hmax₂
  let : EffectiveEpi e₁.hom.hom.left :=
    (isCentralIsogeny_intersectionFactor hG z hz d hT₁ t₁ ht₁ hmax₁ hprod).isIsogeny.effectiveEpi
  let : EffectiveEpi e₂.hom.hom.left :=
    (isCentralIsogeny_intersectionFactor hG z hz d hT₂ t₂ ht₂ hmax₂ hprod).isIsogeny.effectiveEpi
  exact SubgroupFunctor.range_eq_of_fpqc_products
    z (subgroupIntersectionHom d t₁) (subgroupIntersectionHom d t₂)
    (hz.commute_values _) (hz.commute_values _) t₁ e₁
    (intersectionFactor_comp hG z hz d hT₁ t₁ ht₁ hmax₁) t₂ e₂
    (intersectionFactor_comp hG z hz d hT₂ t₂ ht₂ hmax₂)
    (SubgroupFunctor.range_comp_eq_of_range_eq _ _ d hi)

end RelativeDerivedTorus

end Langlands.GroupScheme
