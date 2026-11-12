import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Mathlib.RingTheory.FiniteType

/-! # Picard sheaf of an abelian scheme over a normal finite-type `ℤ`-domain

The Picard sheaf is represented by a scheme in which every finite set of points lies in an
affine open. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every integrally closed domain `R` of finite type over `ℤ` and every abelian scheme `A`
over `Spec R`, the actual fppf Picard class sheaf of `A` is represented by a scheme `P` over
`Spec R` in which every finite set of points lies in an affine open subscheme. -/
def NormalFiniteTypeAbelianPicardSheafAFSchemeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra.FiniteType ℤ R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    ∃ P : Over (Spec (CommRingCat.of R)),
      PointTopology.HasFiniteAffineNeighborhoods P.left ∧
        Nonempty ((RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P)

end Langlands.AlgebraicGeometry.Picard
