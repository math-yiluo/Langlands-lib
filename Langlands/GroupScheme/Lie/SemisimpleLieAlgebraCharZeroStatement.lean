import Langlands.GroupScheme.Lie.AffineBracket
import Langlands.GroupScheme.Reductive.Semisimple
import Mathlib.Algebra.Lie.Semisimple.Defs

/-! # The Lie algebra of a semisimple group in characteristic zero -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

/-- Over a field of characteristic zero, the actual tangent Lie algebra of a semisimple
group has no nonzero solvable ideal. -/
def SemisimpleLieAlgebraCharZeroStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom], IsSemisimple G →
      letI := instAffineKernelLieRing (R := CommRingCat.of k) (A := CommRingCat.of k) G
      letI := instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := CommRingCat.of k) G
      LieAlgebra.HasTrivialRadical (CommRingCat.of k) (Additive (lieKernel G (CommRingCat.of k)))

end Langlands.GroupScheme.Lie
