import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Ring-valued points of algebraic spaces and diagonal conditions

Quasi-separatedness and separatedness of an algebraic space are conditions on the
actual diagonal of its presheaf, tested on every represented scheme pullback.
For an algebraic space over `Spec C` and a `C`-algebra `A`, the `A`-valued points
are the sections over the actual spectrum `Spec A`; for an actual scheme they are
identified with its relative scheme points.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Quasi-separatedness: the diagonal is representable and every represented
projection of it is a quasi-compact scheme morphism. -/
def IsQuasiSeparated (X : AlgebraicSpace S) : Prop :=
  (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.QuasiCompact.{u})
    (Over.forget S)).relative (schemeYoneda S) (diag X.presheaf)

/-- Separatedness: the diagonal is a representable closed immersion. -/
def IsSeparated (X : AlgebraicSpace S) : Prop :=
  IsClosedImmersion (diag X.presheaf)

variable (C : Type u) [CommRing C]

/-- The `A`-valued points of an algebraic space over `Spec C`: its sections over the
actual spectrum of the `C`-algebra `A`. -/
def RingPoints (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (A : Type u) [CommRing A] [Algebra C A] : Type (u + 1) :=
  X.sections (ringTest C A)

namespace RingPoints

variable {C}
variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra C A] [Algebra C B] [Algebra C D]
variable {X Y Z : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- A morphism of algebraic spaces evaluated on `A`-valued points. -/
def map (f : X ⟶ Y) : RingPoints C X A → RingPoints C Y A :=
  mapSections f (ringTest C A)

/-- Change of coefficient algebra along a `C`-algebra map, by pulling back along
the actual morphism of spectra. -/
def changeRing (φ : A →ₐ[C] B) : RingPoints C X A → RingPoints C X B :=
  X.pullback (ringTestMap C φ)

@[simp]
theorem map_id (x : RingPoints C X A) : map (𝟙 X) x = x := rfl

@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : RingPoints C X A) :
    map (f ≫ g) x = map g (map f x) := rfl

/-- Evaluation of a morphism commutes with change of coefficient algebra. -/
theorem changeRing_map (f : X ⟶ Y) (φ : A →ₐ[C] B) (x : RingPoints C X A) :
    changeRing φ (map f x) = map f (changeRing φ x) :=
  mapSections_naturality f (ringTestMap C φ) x

end RingPoints

/-- For an actual scheme over `Spec C`, the `A`-valued points of the associated
algebraic space are its relative scheme points. -/
def schemeRingPointsEquiv (U : Over (Spec (CommRingCat.of C)))
    (A : Type u) [CommRing A] [Algebra C A] :
    RingPoints C ((schemeToSpace _).obj U) A ≃ RingPoint C U A :=
  Equiv.ulift

variable {C}

/-- The scheme comparison is natural in actual scheme morphisms. -/
theorem schemeRingPointsEquiv_map {U V : Over (Spec (CommRingCat.of C))}
    {A : Type u} [CommRing A] [Algebra C A] (g : U ⟶ V)
    (x : RingPoints C ((schemeToSpace _).obj U) A) :
    schemeRingPointsEquiv C V A (RingPoints.map ((schemeToSpace _).map g) x) =
      schemeRingPointsEquiv C U A x ≫ g :=
  rfl

/-- The scheme comparison is natural in the coefficient algebra. -/
theorem schemeRingPointsEquiv_changeRing {U : Over (Spec (CommRingCat.of C))}
    {A B : Type u} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
    (φ : A →ₐ[C] B) (x : RingPoints C ((schemeToSpace _).obj U) A) :
    schemeRingPointsEquiv C U B (RingPoints.changeRing φ x) =
      ringTestMap C φ ≫ schemeRingPointsEquiv C U A x :=
  rfl

end Langlands.AlgebraicGeometry.AlgebraicSpace
