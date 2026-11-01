import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement
import Langlands.AbelianScheme.Multiplication

/-! # Multiplication invariance of the actual two-power torsion closure -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- The Zariski closure of the actual geometric two-power torsion locus is
invariant under both full inverse image and image by multiplication by two. -/
def TwoPowerTorsionClosureInvarianceStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (A : AbelianScheme (Spec (CommRingCat.of K))),
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left ⁻¹'
        closure (twoPowerTorsionLocus A) = closure (twoPowerTorsionLocus A) ∧
      (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left ''
        closure (twoPowerTorsionLocus A) = closure (twoPowerTorsionLocus A)

end Langlands.AbelianScheme.Tate
