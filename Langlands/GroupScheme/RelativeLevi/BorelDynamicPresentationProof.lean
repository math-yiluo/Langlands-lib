import Langlands.GroupScheme.RelativeLevi.BorelDynamicPresentationStatement
import Langlands.GroupScheme.RelativeLevi.RelativeBorelDynamicCover
import Langlands.GroupScheme.RelativeLevi.BorelDynamicCompositePresentation

/-! # Étale-local dynamic presentation of the given Borel pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem dynamicPresentationClause_of_data
    {S U : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (b : U ⟶ S)
    (E : RelativeLevi.BorelDynamicPresentationData i T t b) :
    IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp ∧
      ∃ ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T),
        let χ := CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map t
        SubgroupFunctor.range ((GroupScheme.baseChange b).map i) = Dynamic.parabolic χ ∧
          Dynamic.centralizer χ =
            SubgroupFunctor.range ((GroupScheme.baseChange b).map t) ∧
          ∃ (C : GroupScheme U) (j : C ⟶ (GroupScheme.baseChange b).obj G),
            IsRelativeBorelSubgroup j ∧
              SubgroupFunctor.range j =
                Dynamic.parabolic (Dynamic.oppositeCocharacter χ) :=
  ⟨E.split, E.cocharacter, E.positive, E.centralizer,
    E.negative.obj, E.negative.inclusion, E.negative.borel, E.negative.range_eq⟩

/-- The specified Borel and maximal torus have the full local dynamic
presentation, including the actual negative relative Borel representative. -/
theorem relativeBorelDynamicPresentation : RelativeBorelDynamicPresentationStatement.{u} := by
  intro S G B i T t hG hT ht hmax hi hti
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    RelativeBorelDynamicPresentation.splittingCover T hT
  let D : ∀ (a : 𝒱.I₀) (s : 𝒱.X a),
      RelativeLevi.BorelDynamicNeighbourhoodData ((GroupScheme.baseChange (𝒱.f a)).map i)
        ((CommGroupScheme.baseChange (𝒱.f a)).obj T)
        ((GroupScheme.baseChange (𝒱.f a)).map t) s := by
    intro a s
    have : Etale (𝒱.f a) := 𝒱.map_prop a
    have hsplit : IsSplitTorus ((CommGroupScheme.baseChange (𝒱.f a)).obj T).toGrp :=
      RelativeBorelDynamicPresentation.splittingCover_split T hT a
    exact borelDynamicNeighbourhoodAt
      (S := 𝒱.X a) (G := (GroupScheme.baseChange (𝒱.f a)).obj G)
      (B := (GroupScheme.baseChange (𝒱.f a)).obj B)
      ((GroupScheme.baseChange (𝒱.f a)).map i) ((CommGroupScheme.baseChange (𝒱.f a)).obj T)
      ((GroupScheme.baseChange (𝒱.f a)).map t) (hG.baseChange (𝒱.f a)) hsplit
      (ht.baseChange (𝒱.f a)) (hmax.baseChange (𝒱.f a)) (hi.baseChange_of_etale (𝒱.f a))
      (RelativeBorelDynamicPresentation.torus_range_le_baseChange i T t hti (𝒱.f a)) s
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    RelativeBorelDynamicPresentation.coverOfNeighbourhoods i T t 𝒱 D
  refine ⟨𝒰, ?_⟩
  rintro ⟨a, s⟩
  let E := borelDynamicCompositePresentation
    (S := S) (G := G) (B := B) i T t (𝒱.f a) (s := s) (D a s)
  have hf : 𝒰.f ⟨a, s⟩ = (D a s).projection ≫ 𝒱.f a := rfl
  dsimp only
  rw [hf]
  exact dynamicPresentationClause_of_data i T t _ E

end Langlands.GroupScheme
