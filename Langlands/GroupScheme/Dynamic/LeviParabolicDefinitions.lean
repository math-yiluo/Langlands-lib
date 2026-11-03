import Langlands.GroupScheme.SubgroupFunctorProduct
import Langlands.GroupScheme.Rational.ParabolicFunctor
import Langlands.GroupScheme.Dynamic.Decomposition

/-! # Extension from a represented dynamic centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G L : GroupScheme S}
  (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
  (hj : (centralizer χ).IsRepresentedBy j)

include hj in
/-- The image of any subgroup functor of the represented centralizer lies in
the dynamic parabolic. -/
theorem map_fromCentralizer_le_parabolic (F : SubgroupFunctor L) :
    F.map j ≤ parabolic χ := by
  apply (SubgroupFunctor.map_le_range j F).trans
  rw [hj.2]
  exact centralizer_le_parabolic χ

include hj in
/-- The unipotent functor is normalized by the image of every subgroup
functor of the represented centralizer. -/
theorem unipotent_isNormalizedBy_map_fromCentralizer (F : SubgroupFunctor L) :
    (unipotent χ).IsNormalizedBy (F.map j) :=
  fun T _g _n hg hn =>
    conj_mem_unipotent χ (map_fromCentralizer_le_parabolic χ j hj F T hg) hn

/-- Extend a subgroup functor `F` of a represented centralizer by the ambient
unipotent functor, with exact products over each original test scheme. -/
def extendFromCentralizer (F : SubgroupFunctor L) : SubgroupFunctor G :=
  SubgroupFunctor.normalizedProduct (F.map j) (unipotent χ)
    (unipotent_isNormalizedBy_map_fromCentralizer χ j hj F)

theorem mem_extendFromCentralizer (F : SubgroupFunctor L) (T : Over S) (x : T ⟶ G.X) :
    x ∈ (extendFromCentralizer χ j hj F).carrier T ↔
      ∃ l ∈ F.carrier T, ∃ n ∈ (unipotent χ).carrier T,
        (l ≫ j.hom.hom) * n = x := by
  constructor
  · rintro ⟨a, ⟨l, hl, rfl⟩, n, hn, rfl⟩
    exact ⟨l, hl, n, hn, rfl⟩
  · rintro ⟨l, hl, n, hn, rfl⟩
    exact ⟨l ≫ j.hom.hom, ⟨l, hl, rfl⟩, n, hn, rfl⟩

theorem extendFromCentralizer_isPointwiseProduct (F : SubgroupFunctor L) :
    (extendFromCentralizer χ j hj F).IsPointwiseProduct (F.map j) (unipotent χ) :=
  SubgroupFunctor.normalizedProduct_isPointwiseProduct _ _ _

theorem extendFromCentralizer_le_parabolic (F : SubgroupFunctor L) :
    extendFromCentralizer χ j hj F ≤ parabolic χ :=
  SubgroupFunctor.normalizedProduct_le _
    (map_fromCentralizer_le_parabolic χ j hj F) (unipotent_le_parabolic χ)

theorem extendFromCentralizer_mono {F F' : SubgroupFunctor L} (h : F ≤ F') :
    extendFromCentralizer χ j hj F ≤ extendFromCentralizer χ j hj F' :=
  SubgroupFunctor.normalizedProduct_mono _ _ (SubgroupFunctor.map_mono j h) le_rfl

section IdentityTest

variable {k : Type u} [Field k]
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (j : L ⟶ G) (hj : (centralizer χ).IsRepresentedBy j)

/-- The exact extension formula on the same identity-test carriers used for
the dynamic semidirect decomposition of rational points. -/
theorem mem_extendFromCentralizer_rationalPointSubgroup
    (F : SubgroupFunctor L) (x : RationalPoint k G.X) :
    x ∈ (extendFromCentralizer χ j hj F).rationalPointSubgroup ↔
      ∃ l ∈ F.rationalPointSubgroup,
        ∃ n ∈ (unipotent χ).rationalPointSubgroup,
          (l ≫ j.hom.hom) * n = x :=
  mem_extendFromCentralizer χ j hj F _ x

/-- Dynamic parabolic points inside a closed subgroup are the actual
intersection with the ambient dynamic parabolic on identity-test points. -/
theorem parabolic_map_rationalPointSubgroup (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L)
    (hjc : IsClosedSubgroup j) :
    ((parabolic ν).map j).rationalPointSubgroup =
      (SubgroupFunctor.range j).rationalPointSubgroup ⊓
        (parabolic (ν ≫ j)).rationalPointSubgroup := by
  rw [← range_inf_parabolic ν j hjc, SubgroupFunctor.rationalPointSubgroup_inf]

/-- The corresponding exact identity-test centralizer intersection. -/
theorem centralizer_map_rationalPointSubgroup
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L) (hjc : IsClosedSubgroup j) :
    ((centralizer ν).map j).rationalPointSubgroup =
      (SubgroupFunctor.range j).rationalPointSubgroup ⊓
        (centralizer (ν ≫ j)).rationalPointSubgroup := by
  rw [← range_inf_centralizer ν j hjc, SubgroupFunctor.rationalPointSubgroup_inf]

/-- The corresponding exact identity-test unipotent intersection. -/
theorem unipotent_map_rationalPointSubgroup
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L) (hjc : IsClosedSubgroup j) :
    ((unipotent ν).map j).rationalPointSubgroup =
      (SubgroupFunctor.range j).rationalPointSubgroup ⊓
        (unipotent (ν ≫ j)).rationalPointSubgroup := by
  rw [← range_inf_unipotent ν j hjc, SubgroupFunctor.rationalPointSubgroup_inf]

end IdentityTest

end Langlands.GroupScheme.Dynamic
