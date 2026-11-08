import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationReduction
import Langlands.GroupScheme.Rational.TorusFormalCharacter
import Langlands.GroupScheme.Rational.DominantHighestWeightProof
import Langlands.GroupScheme.Reductive.RootDatumExistence

/-! # Class functions separate conjugacy classes of maximal-torus points -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.DominantTriangular

namespace Langlands.GroupScheme

namespace SplitPinning

/-- **Triangular character data from highest-weight representations.** Over an algebraically
closed field, for two rational points of the torus of a split pinning with the same image in
the class-function quotient, every dominant `lam` admits a function on the character lattice
that is invariant under the reflection group, equals `1` at `lam`, is supported below `lam`,
and has the same character sums at both points: the formal character of a highest-weight
representation of weight `lam`. -/
theorem exists_isInvariant_triangular_of_rho_eq {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (p : SplitPinning G)
    (s t : rationalPoints p.torus.toGrp)
    (h : (s ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G =
      (t ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G)
    (lam : characterLattice p.torus) (hlam : p.IsDominantWeight lam) :
    ∃ c : characterLattice p.torus →₀ k,
      LinearAlgebra.DominantTriangular.IsInvariant (reflectionGroup p.rootDatum) c ∧
        c lam = 1 ∧ (∀ ν, c ν ≠ 0 → lam - ν ∈ p.positiveRootMonoid) ∧
        evalChar (characterValues s) c = evalChar (characterValues t) c := by
  obtain ⟨n, ρ, hρ⟩ := splitDominantHighestWeightRepresentationsExist k G p lam hlam
  obtain ⟨c, hinv, hlam1, hsupp, hsum⟩ := p.exists_invariant_triangular_of_rho_eq ρ lam hρ s t h
  refine ⟨c, isInvariant_reflectionGroup_of_reflection hinv, hlam1, hsupp, ?_⟩
  rw [evalChar_apply, evalChar_apply]
  simpa only [characterValues_apply] using hsum

end SplitPinning

namespace ClassFunctions

/-- **Torus separation** (Steinberg 1965, Corollary 6.6, (b) implies (a)). Over an
algebraically closed field, two rational points of a maximal torus of a connected semisimple
group with the same image in the class-function quotient are conjugate by a rational point
of the group. -/
theorem torusSeparation : TorusSeparationStatement.{u} :=
  torusSeparation_of_triangular rootDatumExistence fun _ _ _ _ _ p s t h lam hlam =>
    p.exists_isInvariant_triangular_of_rho_eq s t h lam hlam

end ClassFunctions

end Langlands.GroupScheme
