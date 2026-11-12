import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.RingTheory.FiniteType

/-! # Scheme representability of the Picard sheaf of an abelian scheme over a finite-type
`ℤ`-algebra -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every commutative ring `R` of finite type over `ℤ` and every abelian scheme `A`
over `Spec R`, the actual fppf Picard class sheaf of `A` is represented by a scheme over
`Spec R`. -/
def FiniteTypeAbelianPicardSheafSchemeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    ∃ P : Over (Spec (CommRingCat.of R)),
      Nonempty ((RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P)

end Langlands.AlgebraicGeometry.Picard
