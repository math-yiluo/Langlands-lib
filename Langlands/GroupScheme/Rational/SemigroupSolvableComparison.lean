import Langlands.GroupScheme.Rational.SemigroupSolvableIntersection
import Langlands.GroupScheme.Rational.SemigroupZeroExcludedIntersection
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof

/-! # Semigroup intersection with a connected solvable subgroup -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The solvable alternative of the existing all-test semigroup intersection
comparison, with arbitrary additive subsemigroups and arbitrary field. -/
def SemigroupSolvableIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (_hH : Smooth H.X.hom)
    (hAffG : IsAffineHom G.X.hom) (hAffH : IsAffineHom H.X.hom)
    (_hConnH : ConnectedSpace H.X.left)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
      (j : H ⟶ G),
      IsClosedSubgroup j →
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
        c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom)) →
      letI := hAffG
      letI := hAffH
      ∀ A : AddSubsemigroup (characterLattice S),
        IsSolvableScheme H →
        (semigroupSubgroup b A).comap j = semigroupSubgroup c A

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    [ConnectedSpace H.X.left]

/-- Intersection with an equivariant smooth connected solvable closed subgroup
commutes with the actual semigroup subgroup construction, including when zero
belongs to the semigroup. -/
theorem semigroup_comap_eq_of_connected_solvable
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom))
    (hsolv : IsSolvableScheme H) (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  by_cases hzero : 0 ∈ A
  · exact semigroup_comap_eq_of_solvable_of_zero_mem c hS
      Torus.solvableFixedContainmentConnected hsolv b j heq semigroupRealization
      hj A hzero
  · exact semigroup_comap_eq_of_zero_not_mem b c j heq semigroupRealization
      CoordinateWeights.coordinateSemigroupComparison.2 hS hj A hzero

/-- The full solvable alternative, with its geometric prerequisites supplied
by the published realization, connectedness and coordinate comparison proofs. -/
theorem semigroupSolvableIntersection : SemigroupSolvableIntersectionStatement.{u} := by
  intro k _ G H hG hH hAffG hAffH hConnH S hS b c j hj heq A hsolv
  let := hG
  let := hH
  let := hAffG
  let := hAffH
  let := hConnH
  exact semigroup_comap_eq_of_connected_solvable hS b c j hj heq hsolv A

end Langlands.GroupScheme.RelativeRoot
