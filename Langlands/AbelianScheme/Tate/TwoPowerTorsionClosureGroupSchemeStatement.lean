import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement

/-! # A closed group scheme realizing the actual two-power torsion closure -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- The actual two-power torsion closure is the image of a smooth proper
commutative group scheme under a closed group-scheme immersion. -/
def TwoPowerTorsionClosureGroupSchemeStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ (G : CommGroupScheme (Spec (CommRingCat.of K)))
      (f : G ⟶ A.toCommGroupScheme),
      IsClosedImmersion (CommGroupScheme.hom f) ∧
      Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Set.range (CommGroupScheme.hom f) = closure (twoPowerTorsionLocus A)

end Langlands.AbelianScheme.Tate
