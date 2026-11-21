import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Directness and leading parts of the unnormalized exponent decomposition -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- A finite unnormalized exponent sum is direct. The leading sums of two
decompositions agree if their difference has only nonleading exponents. -/
def EisensteinExponentDirectnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν),
    let X := ComplexCharacterParameter F (fam.P J)
    let Y := AdelicGroupPoints F G → ℂ
    (∀ (s : Finset X) (c : X → Y),
      (∀ lam ∈ s, fam.HasUnnormalizedExponent J lam (c lam)) →
      (∑ lam ∈ s, c lam = 0) → ∀ lam ∈ s, c lam = 0) ∧
    ∀ (s t u : Finset X) (c d b : X → Y),
      (∀ lam ∈ s, fam.HasUnnormalizedExponent J lam (c lam)) →
      (∀ lam ∈ t, fam.HasUnnormalizedExponent J lam (d lam)) →
      (∀ lam ∈ u, fam.HasUnnormalizedExponent J lam (b lam) ∧ ¬ fam.IsLeadingExponent J lam) →
      (∑ lam ∈ s, c lam = (∑ lam ∈ t, d lam) + ∑ lam ∈ u, b lam) →
      fam.leadingSum J s c = fam.leadingSum J t d

end Langlands.Global
