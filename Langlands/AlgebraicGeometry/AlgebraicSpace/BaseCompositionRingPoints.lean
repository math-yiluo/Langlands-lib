import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange

/-! # Ring-valued fibres after composition of bases -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestRestrictScalarsIso)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

/-- Changing an isomorphic test scheme identifies the actual section fibres. -/
def fibreTestIsoEquiv {S : Scheme.{u}} {F G : Presheaf S} (f : F ⟶ G)
    {U V : Over S} (e : U ≅ V) (y : G.obj (op U)) :
    {x : F.obj (op U) // f.app (op U) x = y} ≃
      {x : F.obj (op V) // f.app (op V) x = G.map e.inv.op y} := by
  refine Equiv.subtypeEquiv ((F.mapIso e.op).toEquiv.symm) ?_
  intro x
  change f.app (op U) x = y ↔ f.app (op V) (F.map e.inv.op x) = G.map e.inv.op y
  rw [f.naturality_apply]
  exact (ConcreteCategory.bijective_of_isIso (G.map e.inv.op)).injective.eq_iff.symm

variable (D C A : Type u) [CommRing D] [CommRing C] [CommRing A]
  [Algebra D C] [Algebra D A] [Algebra C A] [IsScalarTower D C A]

/-- A point with its original coefficient action determines a point over the composed base. -/
def ringPointLift (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (x : RingPoints C X A) : RingPoints D (space (Spec.algebraMap D C) X) A :=
  (presheaf (Spec.algebraMap D C) X.presheaf).map
    (ringTestRestrictScalarsIso D C A).inv.op
    (liftSection (Spec.algebraMap D C) X.presheaf (ringTest C A) x)

/-- Forgetting coefficients in this way is injective on the original ring-valued points. -/
theorem ringPointLift_injective (X : AlgebraicSpace (Spec (CommRingCat.of C))) :
    Function.Injective (ringPointLift D C A X) := by
  intro x y h
  apply liftSection_injective (Spec.algebraMap D C) X.presheaf (ringTest C A)
  exact (ConcreteCategory.bijective_of_isIso
    ((presheaf (Spec.algebraMap D C) X.presheaf).map
      (ringTestRestrictScalarsIso D C A).inv.op)).injective h

/-- The point lift commutes with every original space morphism. -/
theorem ringPointLift_map {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (x : RingPoints C X A) :
    RingPoints.map (spaceMap (Spec.algebraMap D C) f) (ringPointLift D C A X x) =
      ringPointLift D C A Y (RingPoints.map f x) := by
  have hn := (map (Spec.algebraMap D C) (hom f)).naturality_apply
    (ringTestRestrictScalarsIso D C A).inv.op
    (liftSection (Spec.algebraMap D C) X.presheaf (ringTest C A) x)
  exact hn.trans (congrArg
    ((presheaf (Spec.algebraMap D C) Y.presheaf).map
      (ringTestRestrictScalarsIso D C A).inv.op)
    (map_liftSection (Spec.algebraMap D C) (hom f) (ringTest C A) x))

/-- A fibre over a lifted target point retains exactly the original coefficient action. -/
def ringPointFibreEquiv {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (y : RingPoints C Y A) :
    {x : RingPoints C X A // RingPoints.map f x = y} ≃
      {x : RingPoints D (space (Spec.algebraMap D C) X) A //
        RingPoints.map (spaceMap (Spec.algebraMap D C) f) x = ringPointLift D C A Y y} :=
  (fibreEquiv (Spec.algebraMap D C) (hom f) (ringTest C A) y).trans
    (fibreTestIsoEquiv (map (Spec.algebraMap D C) (hom f))
      (ringTestRestrictScalarsIso D C A)
      (liftSection (Spec.algebraMap D C) Y.presheaf (ringTest C A) y))

/-- The natural cardinal of every original point fibre equals that of the composed fibre. -/
theorem card_ringPointFibre {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (y : RingPoints C Y A) :
    Nat.card {x : RingPoints C X A // RingPoints.map f x = y} =
      Nat.card {x : RingPoints D (space (Spec.algebraMap D C) X) A //
        RingPoints.map (spaceMap (Spec.algebraMap D C) f) x = ringPointLift D C A Y y} :=
  Nat.card_congr (ringPointFibreEquiv D C A f y)

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
