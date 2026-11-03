import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness and injectivity of coefficient change -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- Injective coefficient maps preserve distinct points of a separated scheme
when the source value ring is reduced. -/
def SchemeSeparatedCoefficientInjectivityProperty [_root_.IsReduced S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
    (f : S →ₐ[R] T), Function.Injective f →
      Function.Injective (RingPoint.changeRing (X := X) f)

end Langlands.AlgebraicGeometry.PointTopology
