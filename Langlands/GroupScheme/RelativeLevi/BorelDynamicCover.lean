import Langlands.GroupScheme.RelativeLevi.BorelDynamicNeighbourhood
import Langlands.GroupScheme.RelativeLevi.BorelResidueCocharacter

/-! # A dynamic presentation cover for a Borel through a split maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B : GroupScheme S}
    (i : B ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)

/-- The full local dynamic Borel data at a point, now with the initial
cocharacter supplied by the residue Borel classification. -/
def borelDynamicNeighbourhoodAt (s : S) :
    RelativeLevi.BorelDynamicNeighbourhoodData i T t s :=
  let d := residueBorelCocharacter hG hT t hmax i hi hti s
  borelDynamicNeighbourhoodOfResidue i T t hG hT ht hmax hi hti s
    d.cocharacter d.parabolic_eq d.centralizer_eq

/-- A small étale cover of dynamic presentation neighbourhoods, indexed by
the points of the original base. -/
def borelDynamicOpenCover : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  Scheme.Cover.mkOfCovers S
    (fun s => (borelDynamicNeighbourhoodAt i T t hG hT ht hmax hi hti s).base)
    (fun s => (borelDynamicNeighbourhoodAt i T t hG hT ht hmax hi hti s).projection)
    (fun s =>
      let d := borelDynamicNeighbourhoodAt i T t hG hT ht hmax hi hti s
      ⟨s, d.contains.choose, d.contains.choose_spec⟩)
    (fun s => by
      have : IsOpenImmersion
          (borelDynamicNeighbourhoodAt i T t hG hT ht hmax hi hti s).projection :=
        (borelDynamicNeighbourhoodAt i T t hG hT ht hmax hi hti s).openImmersion
      infer_instance)

/-- The constructed cover has all clauses of the local dynamic Borel
presentation, for a globally split supplied maximal torus. -/
theorem borelDynamicOpenCover_spec :
    let 𝒰 := borelDynamicOpenCover i T t hG hT ht hmax hi hti
    ∀ a : 𝒰.I₀,
      let G' := (GroupScheme.baseChange (𝒰.f a)).obj G
      let T' := (CommGroupScheme.baseChange (𝒰.f a)).obj T
      let i' := (GroupScheme.baseChange (𝒰.f a)).map i
      let t' := (GroupScheme.baseChange (𝒰.f a)).map t
      IsSplitTorus T'.toGrp ∧
        ∃ ν : cocharacterLattice T',
          let χ := CommGroupScheme.groupHom ν ≫ t'
          SubgroupFunctor.range i' = Dynamic.parabolic χ ∧
            Dynamic.centralizer χ = SubgroupFunctor.range t' ∧
            ∃ (C : GroupScheme (𝒰.X a)) (j : C ⟶ G'),
              IsRelativeBorelSubgroup j ∧
                SubgroupFunctor.range j =
                  Dynamic.parabolic (Dynamic.oppositeCocharacter χ) := by
  dsimp only
  intro a
  let d := borelDynamicNeighbourhoodAt i T t hG hT ht hmax hi hti a
  exact ⟨d.split, d.cocharacter, d.positive, d.centralizer,
    d.negative.obj, d.negative.inclusion, d.negative.borel, d.negative.range_eq⟩

end Langlands.GroupScheme
