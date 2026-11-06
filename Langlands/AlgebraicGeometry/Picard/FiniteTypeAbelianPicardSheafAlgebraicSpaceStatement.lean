import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FiniteType

/-! # The fppf Picard sheaf of an abelian scheme over a finite-type `ℤ`-algebra -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual fppf Picard class sheaf of every abelian scheme over `Spec R`, for a
commutative ring `R` of finite type over `ℤ`, is an algebraic space with an actual
surjective etale scheme atlas locally of finite presentation over `Spec R`. -/
def FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    AlgebraicSpace.IsAlgebraicSpace (Spec (CommRingCat.of R))
        (RelativePicard.classSheaf A.X.hom) ∧
      ∃ (U : Over (Spec (CommRingCat.of R)))
        (a : (AlgebraicSpace.schemeYoneda _).obj U ⟶
          RelativePicard.classSheafPresheaf A.X.hom),
        AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
          LocallyOfFinitePresentation U.hom

end Langlands.AlgebraicGeometry.Picard
