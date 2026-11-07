import Langlands.GroupScheme.Rational.FundamentalRepresentations

/-! # Highest-weight representation existence at integral dominant characters -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- An actual torus character is dominant when its integral pairing with every
simple coroot of the supplied base is nonnegative. -/
def IsDominantWeight (lam : characterLattice p.torus) : Prop :=
  ∀ a : p.base.support, 0 ≤ p.rootDatum.toLinearMap lam (p.rootDatum.coroot a)

end SplitPinning

/-- Every integral dominant character of a supplied split pinning is the highest
weight of an actual finite-dimensional irreducible representation. -/
def SplitDominantHighestWeightRepresentationsExistStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (lam : characterLattice p.torus),
    p.IsDominantWeight lam →
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), p.IsHighestWeight ρ lam

end Langlands.GroupScheme
