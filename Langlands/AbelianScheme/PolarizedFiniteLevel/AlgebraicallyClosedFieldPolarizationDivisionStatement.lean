import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Positive-multiple descent of ample Mumford presentations over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Let `A` be an actual abelian scheme over the spectrum of an algebraically closed
field `K`, with chosen dual witnesses `W`, and let `mu : A ⟶ W.dual P` be an actual
homomorphism. If, for some positive natural number `n`, the underlying map of `n • mu`
is the Mumford map of an ample line bundle on `A` over `K`, then so is the underlying
map of `mu`. This proposition is a statement target, not a proof. -/
def AlgebraicallyClosedFieldPolarizationDivisionStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (W : DualWitness A)
    (mu : A ⟶ W.dual P) (n : ℕ), 0 < n →
      HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
          (groupHom (n • mu)).hom.hom →
        HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
          (groupHom mu).hom.hom

end Langlands.AbelianScheme.PolarizedFiniteLevel
