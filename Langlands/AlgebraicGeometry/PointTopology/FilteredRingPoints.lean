import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Actual relative scheme points along algebra diagrams

The construction underlying Conrad (3.5.1), before the arithmetic specialization
or topology. Relative spectra reuse Mathlib's `algSpec` functor.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- Mathlib's relative spectrum object is exactly the existing test scheme. -/
@[simp]
theorem algSpec_obj_eq_ringTest (A : CommAlgCat.{u} R) :
    (algSpec (CommRingCat.of R)).obj (op A) = ringTest R A := rfl

/-- The existing value-algebra map agrees with Mathlib's relative spectrum map. -/
@[simp]
theorem algSpec_map_eq_ringTestMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    (algSpec (CommRingCat.of R)).map f.op = ringTestMap R f.hom := rfl

/-- The actual point functor on commutative `R`-algebras, including nonaffine targets. -/
def ringPointFunctor (X : Over (Spec (CommRingCat.of R))) :
    CommAlgCat.{u} R ⥤ Type u :=
  (algSpec (CommRingCat.of R)).rightOp ⋙ yoneda.obj X

@[simp]
theorem ringPointFunctor_obj (X : Over (Spec (CommRingCat.of R)))
    (A : CommAlgCat.{u} R) :
    (ringPointFunctor R X).obj A = RingPoint R X A := rfl

@[simp]
theorem ringPointFunctor_map_apply (X : Over (Spec (CommRingCat.of R)))
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) (p : RingPoint R X A) :
    (ringPointFunctor R X).map f p = p.changeRing f.hom := rfl

/-- Postcomposition with a relative scheme morphism on the actual point functors. -/
def ringPointFunctorMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    ringPointFunctor R X ⟶ ringPointFunctor R Y :=
  Functor.whiskerLeft (algSpec (CommRingCat.of R)).rightOp (yoneda.map f)

@[simp]
theorem ringPointFunctorMap_app {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (A : CommAlgCat.{u} R) (p : RingPoint R X A) :
    (ringPointFunctorMap R f).app A p = p ≫ f := rfl

variable {J : Type u} [SmallCategory J] (F : J ⥤ CommAlgCat.{u} R)

/-- The cone of actual relative spectra attached to an algebra cocone. -/
def ringTestCone (c : Cocone F) : Cone (F.op ⋙ algSpec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).mapCone c.op

@[simp]
theorem ringTestCone_π_app (c : Cocone F) (j : J) :
    (ringTestCone R F c).π.app (op j) = ringTestMap R (c.ι.app j).hom := rfl

/-- An algebra colimit gives the actual limit of its relative spectra. -/
def ringTestConeIsLimit (c : Cocone F) (hc : IsColimit c) :
    IsLimit (ringTestCone R F c) := by
  letI : PreservesLimitsOfSize.{u, u} (algSpec (CommRingCat.of R)) :=
    preservesLimitsOfSize_algSpec
  exact isLimitOfPreserves (algSpec (CommRingCat.of R)) hc.op

/-- The actual point cocone induced by a cocone of value algebras. -/
def ringPointCocone (X : Over (Spec (CommRingCat.of R))) (c : Cocone F) :
    Cocone (F ⋙ ringPointFunctor R X) :=
  (ringPointFunctor R X).mapCocone c

@[simp]
theorem ringPointCocone_ι_app (X : Over (Spec (CommRingCat.of R)))
    (c : Cocone F) (j : J) (p : RingPoint R X (F.obj j)) :
    (ringPointCocone R F X c).ι.app j p = p.changeRing (c.ι.app j).hom := rfl

/-- The type colimit of the actual stage point sets, with its usual quotient model. -/
def RingPointColimit (X : Over (Spec (CommRingCat.of R))) : Type u :=
  (F ⋙ ringPointFunctor R X).ColimitType

/-- The canonical class of an actual point at a stage. -/
def ringPointColimitι (X : Over (Spec (CommRingCat.of R))) (j : J) :
    RingPoint R X (F.obj j) → RingPointColimit R F X :=
  (F ⋙ ringPointFunctor R X).ιColimitType j

/-- The canonical comparison from the point colimit to the points over the cocone algebra. -/
def ringPointColimitMap (X : Over (Spec (CommRingCat.of R))) (c : Cocone F) :
    RingPointColimit R F X → RingPoint R X c.pt :=
  (F ⋙ ringPointFunctor R X).descColimitType
    ((F ⋙ ringPointFunctor R X).coconeTypesEquiv.symm (ringPointCocone R F X c))

/-- On a stage point the comparison is the actual value-algebra change map. -/
@[simp]
theorem ringPointColimitMap_ι (X : Over (Spec (CommRingCat.of R)))
    (c : Cocone F) (j : J) (p : RingPoint R X (F.obj j)) :
    ringPointColimitMap R F X c (ringPointColimitι R F X j p) =
      p.changeRing (c.ι.app j).hom := rfl

/-- The underlying morphism is precomposition with the actual spectrum map. -/
@[simp]
theorem ringPointColimitMap_ι_left (X : Over (Spec (CommRingCat.of R)))
    (c : Cocone F) (j : J) (p : RingPoint R X (F.obj j)) :
    (ringPointColimitMap R F X c (ringPointColimitι R F X j p)).left =
      Spec.map (CommRingCat.ofHom (c.ι.app j).hom.toRingHom) ≫ p.left := rfl

/-- Transition maps give the same class in the point colimit. -/
@[simp]
theorem ringPointColimitι_changeRing (X : Over (Spec (CommRingCat.of R)))
    {i j : J} (f : i ⟶ j) (p : RingPoint R X (F.obj i)) :
    ringPointColimitι R F X j (p.changeRing (F.map f).hom) =
      ringPointColimitι R F X i p :=
  (F ⋙ ringPointFunctor R X).ιColimitType_map f p

end Langlands.AlgebraicGeometry.PointTopology
