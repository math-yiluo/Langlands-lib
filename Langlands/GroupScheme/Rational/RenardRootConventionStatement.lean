import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement

/-! # Statement: Renard's radical weights and simple indivisible roots

This comparison uses the actual conjugation action and the actual dynamic
unipotent subgroup. All sets below are formed from published definitions.
The assertion is a structural proof target, not a supplied root-system premise.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The nonzero Lie weights of a generic dynamic radical are precisely the
positive relative roots. Their indivisible part agrees with both published
reduced-positive-root conventions, and its indecomposables agree with the
simple roots defined using all positive relative roots.

This is the arbitrary-field structural comparison underlying Renard V.3.4
and V.3.12. It retains possible nonreduced roots and includes rank zero. -/
def RenardRootConventionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν →
      let U := Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)
      let pos : Set (characterLattice T) :=
        {α | α ≠ 0 ∧
          α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation i) U}
      let redPos := RelativeRoot.indivisibleRoots i ∩ pos
      let simple : Set (characterLattice T) :=
        {α | α ∈ redPos ∧
          ¬ ∃ β ∈ redPos, ∃ γ ∈ redPos, α = β + γ}
      pos = positiveRelativeRoots i ν ∧
      redPos = RelativeRoot.indivisiblePositiveRoots i ν ∧
      redPos = reducedPositiveRelativeRoots i ν ∧
      simple = simpleRelativeRoots i ν

end Langlands.GroupScheme
