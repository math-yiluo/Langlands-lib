import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FiniteType

/-! # Smooth scheme atlases of the Picard stack over a finite-type `ℤ`-algebra: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a proper flat scheme over `Spec R`, where `R` is a commutative ring of
finite type over `ℤ`, the actual relative line-bundle groupoid has a smooth
surjective scheme atlas locally of finite type over `Spec R`. Its point fibres
are represented by schemes on the full slice. -/
def FiniteTypePicardStackAtlasStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (X : Over (Spec (CommRingCat.of R))),
    IsProper X.hom → Flat X.hom →
      PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas X.hom

end Langlands.AlgebraicGeometry.Picard
