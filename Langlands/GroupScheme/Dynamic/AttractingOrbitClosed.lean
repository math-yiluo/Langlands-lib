import Langlands.GroupScheme.Dynamic.FixedAttractingAction

/-! # Closed parabolic orbits of attracted rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SchemeAction

open GmCoordinateAction Dynamic.Affine

section Ring

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} {X : Over (Spec R)}
  [IsAffine H.X.left] [IsAffine X.left]
  (a : SchemeAction H X) (χ : (Gm (Spec R)).toGrp ⟶ H)

/-- The original orbit map restricted along the actual cocharacter parabolic inclusion. -/
def cocharacterParabolicOrbitMap (x : 𝟙_ (Over (Spec R)) ⟶ X) :
    (parabolicScheme χ).X ⟶ X :=
  (parabolicHom χ).hom.hom ≫ a.orbitMap x

/-- Inclusion of the attracted orbit is the original orbit restricted to the actual parabolic. -/
theorem cocharacterAttractingAction_orbitMap_comp
    (x : 𝟙_ (Over (Spec R)) ⟶ schemeActionAttractingScheme (a.cocharacterAction χ)) :
    (a.cocharacterAttractingAction χ).orbitMap x ≫
        schemeActionAttractingHom (a.cocharacterAction χ) =
      a.cocharacterParabolicOrbitMap χ
        (x ≫ schemeActionAttractingHom (a.cocharacterAction χ)) := by
  rw [cocharacterParabolicOrbitMap, orbitMap, cocharacterAttractingAction_act_comp,
    a.comp_orbitMap]
  simp only [Category.id_comp, Category.assoc]

end Ring

section Field

variable {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))} {X : Over (Spec (CommRingCat.of k))}
  [IsAffine H.X.left] [IsAffine X.left] [Smooth H.X.hom] [Smooth X.hom]
  (a : SchemeAction H X) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H)

/-- A smooth actual action relation makes the parabolic orbit of an attracted rational point closed. -/
theorem isClosed_range_parabolic_orbitMap_of_isAttracted
    (hrel : Smooth (lift a.hom (snd H.X X)).left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.cocharacterAction χ).IsAttracted x) :
    IsClosed (Set.range (a.cocharacterParabolicOrbitMap χ x).left) := by
  obtain ⟨y, hy⟩ := (exists_schemeActionAttracting_factor_iff_all
    (a.cocharacterAction χ) x).mpr hx
  have hc := (a.cocharacterAttractingAction χ).isClosed_range_orbitMap
    (a.smooth_cocharacterAttractingAction_relation χ hrel) y
  have hj := (schemeActionAttractingHom (a.cocharacterAction χ)).left.isClosedEmbedding
  have hi := hj.isClosedMap _ hc
  have hi' : IsClosed (Set.range ((a.cocharacterAttractingAction χ).orbitMap y ≫
      schemeActionAttractingHom (a.cocharacterAction χ)).left) := by
    change IsClosed (Set.range
      ((schemeActionAttractingHom (a.cocharacterAction χ)).left ∘
        ((a.cocharacterAttractingAction χ).orbitMap y).left))
    rwa [Set.range_comp]
  rwa [a.cocharacterAttractingAction_orbitMap_comp χ y, hy] at hi'

/-- In particular the actual parabolic orbit of every cocharacter-fixed rational point is closed. -/
theorem isClosed_range_parabolic_orbitMap_of_isFixed
    (hrel : Smooth (lift a.hom (snd H.X X)).left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.cocharacterAction χ).IsFixed x) :
    IsClosed (Set.range (a.cocharacterParabolicOrbitMap χ x).left) :=
  a.isClosed_range_parabolic_orbitMap_of_isAttracted χ hrel x
    (PointwiseSchemeAction.IsFixed.isAttracted _ hx)

end Field

end Langlands.GroupScheme.SchemeAction
