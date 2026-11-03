import Langlands.GroupScheme.SchemeActionRationalPoints
import Mathlib.Topology.LocallyConstant.Basic

/-! # Fixedness for connected smooth actions on finite schemes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Relative rational sections identify with the closed points of a scheme
locally of finite type over an algebraically closed field. -/
def rationalPointEquivClosedPoint
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] :
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) ≃ closedPoints X.left :=
  (show (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) ≃
      {p : Spec (CommRingCat.of k) ⟶ X.left // p ≫ X.hom = 𝟙 _} from
    { toFun := fun p => ⟨p.left, Over.w p⟩
      invFun := fun p => Over.homMk p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (pointEquivClosedPoint X.hom)

/-- Finitely many rational sections force the entire underlying topology to be
discrete, by the Jacobson property. -/
theorem discreteTopology_of_finite_rationalPoints
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    [Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)] :
    DiscreteTopology X.left := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : Finite (closedPoints X.left) :=
    Finite.of_equiv _ (rationalPointEquivClosedPoint X)
  exact JacobsonSpace.discreteTopology (Set.toFinite _)

namespace SchemeAction

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction H X)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated X.hom]

/-- Every rational section in a finite rational-point scheme is fixed by a
connected smooth group, on every scheme test. -/
theorem isFixed_of_finite_rationalPoints
    [Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    a.IsFixed x := by
  have : DiscreteTopology X.left := discreteTopology_of_finite_rationalPoints X
  have hc : IsLocallyConstant (a.orbitMap x).left :=
    (IsLocallyConstant.iff_continuous _).2 (a.orbitMap x).left.continuous
  apply (a.isFixed_iff_rationalPoints x).2
  intro h
  apply (rationalPointEquivClosedPoint X).injective
  apply Subtype.ext
  change (a.act h x).left (IsLocalRing.closedPoint k) =
    x.left (IsLocalRing.closedPoint k)
  have heq := hc.apply_eq_of_preconnectedSpace
    (h.left (IsLocalRing.closedPoint k))
    ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X).left
      (IsLocalRing.closedPoint k))
  change (h ≫ a.orbitMap x).left (IsLocalRing.closedPoint k) =
    ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) ≫ a.orbitMap x).left
      (IsLocalRing.closedPoint k) at heq
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
    toUnit_unique _ _
  simpa only [a.comp_orbitMap, hu, Category.id_comp, a.act_one] using heq

/-- Every rational section of a scheme with finitely many underlying points is
fixed by a connected smooth group, even if the target is nonreduced. -/
theorem isFixed_of_finite [Finite X.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    a.IsFixed x := by
  have : Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :=
    Finite.of_equiv _ (rationalPointEquivClosedPoint X).symm
  exact a.isFixed_of_finite_rationalPoints x

end SchemeAction

end Langlands.GroupScheme
