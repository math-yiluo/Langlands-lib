import Langlands.GroupScheme.Reductive.StarActionQuasiSplitStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal

/-! # Splitting of a quasi-split group from its absolute star action -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A quasi-split reductive group has a split maximal torus exactly when
the absolute star action on the full based root datum is trivial. -/
def QuasiSplitStarCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsQuasiSplit G → ∀ d : GaloisPinningData k (SeparableClosure k) G,
      HasSplitMaximalTorus G ↔ ∀ σ, d.starAction σ = 1

end Langlands.GroupScheme
