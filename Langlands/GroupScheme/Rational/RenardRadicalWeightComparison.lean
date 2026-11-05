import Langlands.GroupScheme.Rational.RenardRootConventionStatement
import Langlands.GroupScheme.Rational.ActionWeightSupport
import Langlands.GroupScheme.Dynamic.UnipotentPositiveWeights

/-! # Actual radical weights and the two indivisible-positive conventions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The entire actual tangent-weight support of a dynamic radical is its
positive relative-root set. Neither semigroup realization nor reductivity is
needed. -/
theorem actionWeightSupport_dynamicUnipotent_of_locallyOfFiniteType
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    actionWeightSupport (AutomorphicAction.conjugation i)
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) =
        positiveRelativeRoots i ν := by
  rw [← actionWeightSupport_top_inter_positiveSemigroup i ν]
  apply actionWeightSupport_eq_inter_of_hasLieImage
  · exact (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
      (tangentSubmodule_unipotent_eq_semigroupWeightSpan hT i ν)
  · exact actionWeightSupport_subset_positive_of_le_unipotent hT i ν le_rfl

/-- Excluding zero from the dynamic radical's support changes nothing and
identifies exactly the first set in the Renard comparison. -/
theorem nonzero_actionWeightSupport_dynamicUnipotent
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    {α | α ≠ 0 ∧ α ∈ actionWeightSupport (AutomorphicAction.conjugation i)
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))} =
        positiveRelativeRoots i ν := by
  rw [actionWeightSupport_dynamicUnipotent_of_locallyOfFiniteType hT i ν]
  ext α
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- Testing indivisibility before positivity agrees with intersecting the
actual indivisible roots and positive roots. -/
theorem indivisibleRoots_inter_positiveRelativeRoots
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    indivisibleRoots i ∩ positiveRelativeRoots i ν = indivisiblePositiveRoots i ν := by
  ext α
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.1, h.2⟩⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- The two published reduced-positive conventions differ only in the order
of tests and the equivalent natural-number bounds `1 < n` and `2 ≤ n`. -/
theorem indivisiblePositiveRoots_eq_reducedPositiveRelativeRoots
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    indivisiblePositiveRoots i ν = reducedPositiveRelativeRoots i ν := by
  ext α
  constructor
  · rintro ⟨⟨hα, hind⟩, hpos⟩
    exact ⟨⟨hα, hpos⟩, fun n hn β hβ => hind β hβ n (by omega)⟩
  · rintro ⟨⟨hα, hpos⟩, hind⟩
    exact ⟨⟨hα, fun β hβ n hn => hind n (by omega) β hβ⟩, hpos⟩

/-- The first three set comparisons in the Renard root convention, for a fixed
torus map and cocharacter. -/
def RadicalWeightComparisons
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) : Prop :=
    let U := Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)
    let pos : Set (characterLattice T) :=
      {α | α ≠ 0 ∧ α ∈ actionWeightSupport (AutomorphicAction.conjugation i) U}
    let redPos := indivisibleRoots i ∩ pos
    pos = positiveRelativeRoots i ν ∧
      redPos = indivisiblePositiveRoots i ν ∧
      redPos = reducedPositiveRelativeRoots i ν

/-- All three radical-weight and indivisible-positive comparisons from the
Renard aggregate hold for every split torus map into an affine group of local
finite type, without a root-system hypothesis. -/
theorem renardRadicalWeightComparisons
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    RadicalWeightComparisons i ν := by
  dsimp only [RadicalWeightComparisons]
  rw [nonzero_actionWeightSupport_dynamicUnipotent hT i ν,
    indivisibleRoots_inter_positiveRelativeRoots i ν,
    indivisiblePositiveRoots_eq_reducedPositiveRelativeRoots i ν]
  exact ⟨rfl, rfl, rfl⟩

end RelativeRoot

end Langlands.GroupScheme
