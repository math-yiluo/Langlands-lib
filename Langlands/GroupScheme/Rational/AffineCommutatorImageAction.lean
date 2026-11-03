import Langlands.GroupScheme.Rational.AffineCommutatorImageStability
import Langlands.GroupScheme.Rational.PointedCoordinateAction

/-! # The actual pointed action on the affine commutator image -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

open PointedCoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

instance imageInclusion_mono (i : H ⟶ G) (j : K ⟶ G) :
    Mono (imageInclusion i j) := by
  let : IsClosedImmersion (imageInclusion i j).left := imageInclusion_closed i j
  exact Over.mono_of_mono_left _

variable (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (d : AutomorphicAction S.toGrp K) (i : H ⟶ G) (j : K ⟶ G)
    (hi : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (hj : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (h : T ⟶ K.X),
      d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom))

/-- The ambient action restricts to an actual pointed scheme action on its
closed commutator image. -/
def imageAction : PointedAction S (imageScheme i j) :=
  PointedAction.ofStableInclusion b (imageInclusion i j)
    (imageOrigin i j) (imageOrigin_comp i j)
    (imageInclusion_isStable b c d i j hi hj)

@[simp] theorem imageAction_origin :
    (imageAction b c d i j hi hj).origin = imageOrigin i j := rfl

/-- The restricted action agrees with the ambient action on every test scheme. -/
theorem imageAction_act_comp {T : Over (Spec (CommRingCat.of k))}
    (s : T ⟶ S.X) (v : T ⟶ imageScheme i j) :
    (imageAction b c d i j hi hj).act s v ≫ imageInclusion i j =
      b.act s (v ≫ imageInclusion i j) :=
  PointedAction.ofStableInclusion_act_comp b (imageInclusion i j)
    (imageOrigin i j) (imageOrigin_comp i j)
    (imageInclusion_isStable b c d i j hi hj) s v

/-- The closed image inclusion preserves the actual action and fixed point. -/
theorem imageInclusion_isPointedEquivariant :
    IsPointedEquivariant (imageAction b c d i j hi hj)
      (PointedAction.ofGroup b) (imageInclusion i j) :=
  stableInclusion_isPointedEquivariant b (imageInclusion i j)
    (imageOrigin i j) (imageOrigin_comp i j)
    (imageInclusion_isStable b c d i j hi hj)

/-- The actual product-to-image factor intertwines the two input actions with
the image action on every test scheme. -/
theorem imageFactor_equivariant {T : Over (Spec (CommRingCat.of k))}
    (s : T ⟶ S.X) (h : T ⟶ H.X) (h' : T ⟶ K.X) :
    lift (c.act s h) (d.act s h') ≫ imageFactor i j =
      (imageAction b c d i j hi hj).act s (lift h h' ≫ imageFactor i j) := by
  apply (cancel_mono (imageInclusion i j)).1
  rw [imageAction_act_comp, Category.assoc, imageFactor_comp, Category.assoc,
    imageFactor_comp]
  exact commutatorHom_equivariant b c d i j hi hj s h h'

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
