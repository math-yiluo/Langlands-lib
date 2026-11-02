import Langlands.AbelianScheme.FiniteEtaleQuotient
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Existence of quotients of projectively embedded abelian schemes by finite étale subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a locally noetherian base `S`, an abelian scheme `A` with a closed immersion over `S`
into relative projective `n`-space has quotient data for every finite étale closed subgroup
`K`: an abelian scheme `B` and a finite, étale, surjective homomorphism `A ⟶ B` whose scheme
kernel is exactly `K`. This is a theorem target. -/
def FiniteEtaleQuotientExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (A : AbelianScheme S) (n : ℕ)
    (i : A.X.left ⟶ Langlands.AlgebraicGeometry.RelativeProjectiveSpace S n)
    [IsClosedImmersion i],
    i ≫ Langlands.AlgebraicGeometry.RelativeProjectiveSpace.toBase S n = A.X.hom →
      ∀ K : FiniteEtaleSubgroup A, Nonempty K.QuotientData

end Langlands.AbelianScheme
