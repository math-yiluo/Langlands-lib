import Langlands.GroupScheme.AutomorphicAction.CocycleModel

/-! # One affine finite-type model containing the trivial cocycle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.AutomorphicAction

/-- An action of affine finite-type group schemes over a field admits a
conjugation-stable affine finite-type model of actual cocycles containing the
trivial cocycle. This does not assert representability of the whole functor. -/
def AffineFiniteTypeCocycleModelStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (a : AutomorphicAction H G),
      ∃ M : a.CocycleModel, IsAffineHom M.scheme.hom ∧
        LocallyOfFiniteType M.scheme.hom

end Langlands.GroupScheme.AutomorphicAction
