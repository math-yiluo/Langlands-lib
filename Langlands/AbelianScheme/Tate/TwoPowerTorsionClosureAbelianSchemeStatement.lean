import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement

/-! # An abelian scheme realizing the actual two-power torsion closure -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- In characteristic zero, the actual two-power torsion closure is the image
of a closed immersion of actual abelian schemes. -/
def TwoPowerTorsionClosureAbelianSchemeStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (A : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ (B : AbelianScheme (Spec (CommRingCat.of K))) (f : B ⟶ A),
      IsClosedImmersion (AbelianScheme.hom f) ∧
      Set.range (AbelianScheme.hom f) = closure (twoPowerTorsionLocus A)

end Langlands.AbelianScheme.Tate
