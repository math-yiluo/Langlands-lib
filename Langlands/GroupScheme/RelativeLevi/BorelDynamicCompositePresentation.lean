import Langlands.GroupScheme.RelativeLevi.BorelDynamicNeighbourhood
import Langlands.GroupScheme.RelativeLevi.BorelEtaleTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Dynamic Borel presentation over a composite base map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeLevi

/-- Actual dynamic Borel presentation in the direct pullback along a specified
base map, including the chosen negative Borel. -/
structure BorelDynamicPresentationData
    {S U : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (b : U ⟶ S) where
  split : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp
  cocharacter : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)
  positive :
    SubgroupFunctor.range ((GroupScheme.baseChange b).map i) =
      Dynamic.parabolic (CommGroupScheme.groupHom cocharacter ≫
        (GroupScheme.baseChange b).map t)
  centralizer :
    Dynamic.centralizer (CommGroupScheme.groupHom cocharacter ≫
        (GroupScheme.baseChange b).map t) =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map t)
  negative : DynamicBorelData
    (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom cocharacter ≫
      (GroupScheme.baseChange b).map t))

end RelativeLevi

/-- Carry a neighbourhood presentation after base change into the direct
pullback along the composite map, retaining its chosen negative Borel source. -/
def borelDynamicCompositePresentation
    {S U : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (b : U ⟶ S)
    {s : U}
    (D : RelativeLevi.BorelDynamicNeighbourhoodData
      ((GroupScheme.baseChange b).map i)
      ((CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t) s) :
    RelativeLevi.BorelDynamicPresentationData i T t (D.projection ≫ b) := by
  let q := D.projection
  let r := q ≫ b
  let eG := Descent.pullbackComparison b q r rfl G
  let eT := Descent.pullbackComparison b q r rfl T.toGrp
  let ν : cocharacterLattice ((CommGroupScheme.baseChange r).obj T) :=
    D.cocharacter ≫ (CommGroupScheme.isoOfGroupIso eT).hom
  let χ := CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange r).map t
  let χ₀ := CommGroupScheme.groupHom D.cocharacter ≫
    (GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map t)
  have hχ : χ = χ₀ ≫ eG.hom := by
    change (CommGroupScheme.groupHom D.cocharacter ≫ eT.hom) ≫
      (GroupScheme.baseChange r).map t = _
    rw [Category.assoc, ← Descent.pullbackComparison_naturality]
    exact (Category.assoc _ _ _).symm
  have hi : SubgroupFunctor.range ((GroupScheme.baseChange r).map i) =
      (SubgroupFunctor.range
        ((GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map i))).comap eG.inv := by
    rw [← SubgroupFunctor.range_comp_iso]
    rw [Descent.pullbackComparison_naturality, SubgroupFunctor.range_iso_comp]
  have ht : SubgroupFunctor.range ((GroupScheme.baseChange r).map t) =
      (SubgroupFunctor.range
        ((GroupScheme.baseChange q).map ((GroupScheme.baseChange b).map t))).comap eG.inv := by
    rw [← SubgroupFunctor.range_comp_iso]
    rw [Descent.pullbackComparison_naturality, SubgroupFunctor.range_iso_comp]
  have hP : Dynamic.parabolic χ = (Dynamic.parabolic χ₀).comap eG.inv := by
    simpa only [hχ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using Dynamic.parabolic_eq_comap_of_iso χ eG.symm
  have hZ : Dynamic.centralizer χ = (Dynamic.centralizer χ₀).comap eG.inv := by
    simpa only [hχ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using Dynamic.centralizer_eq_comap_of_iso χ eG.symm
  have hneg : Dynamic.oppositeCocharacter χ =
      Dynamic.oppositeCocharacter χ₀ ≫ eG.hom := by
    simp only [hχ, Dynamic.oppositeCocharacter, Category.assoc]
  refine
    { split := IsSplitTorus.of_iso eT.symm D.split
      cocharacter := ν
      positive := ?_
      centralizer := ?_
      negative :=
        { obj := D.negative.obj
          inclusion := D.negative.inclusion ≫ eG.hom
          borel := D.negative.borel.comp_iso eG
          closed := D.negative.closed.comp_iso eG
          range_eq := ?_ } }
  · change SubgroupFunctor.range ((GroupScheme.baseChange r).map i) =
      Dynamic.parabolic χ
    rw [hi, hP, D.positive]
  · change Dynamic.centralizer χ =
      SubgroupFunctor.range ((GroupScheme.baseChange r).map t)
    rw [hZ, ht, D.centralizer]
  · change SubgroupFunctor.range (D.negative.inclusion ≫ eG.hom) =
      Dynamic.parabolic (Dynamic.oppositeCocharacter χ)
    rw [SubgroupFunctor.range_comp_iso, D.negative.range_eq]
    symm
    simpa only [hneg, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using
      Dynamic.parabolic_eq_comap_of_iso (Dynamic.oppositeCocharacter χ) eG.symm

end Langlands.GroupScheme
