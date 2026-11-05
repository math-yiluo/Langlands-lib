# Actual radical weights and the two indivisible-positive conventions

This internal derived module proves the first three set equalities of
`Langlands.GroupScheme.RenardRootConventionStatement`. The Prop-valued definition
`RelativeRoot.RadicalWeightComparisons i ν` packages these three equalities,
using exactly the local `U`, `pos` and `redPos` sets of that aggregate. Its theorem
`RelativeRoot.renardRadicalWeightComparisons` proves this proposition assuming
only an affine group of local
finite type over an arbitrary field, a split torus, a homomorphism from that
torus, and a cocharacter. It requires no smoothness, connectedness, reductivity,
maximality, genericity or semigroup-realization premise. In the exact aggregate,
connected reductivity supplies affineness and smoothness (hence local finite
type), and maximal splitness supplies splitness of the torus.

`RelativeRoot.actionWeightSupport_dynamicUnipotent_of_locallyOfFiniteType` first identifies the entire
actual support, including the question of the zero character. The published
`tangentSubmodule_unipotent_eq_semigroupWeightSpan` gives the exact tangent
submodule of `Dynamic.unipotent (groupHom ν ≫ i)` as the strictly positive
conjugation weight span. The published
`actionWeightSupport_subset_positive_of_le_unipotent` gives the complementary
support bound by taking the subgroup inclusion to be reflexivity. These facts
supply the exact Lie-image and support hypotheses of
`actionWeightSupport_eq_inter_of_hasLieImage`. That theorem identifies the
support with the whole-group support intersected with the positive pairing
semigroup. The published
`actionWeightSupport_top_inter_positiveSemigroup` identifies this intersection
with the actual positive relative roots. Thus the proof never assumes
semigroup realization or replaces the dynamic subgroup with a hypothetical
root subgroup.

`nonzero_actionWeightSupport_dynamicUnipotent` removes the redundant explicit
nonzero filter: every positive relative root is already a nonzero actual Lie
root. The next two lemmas compare existing definitions by set extensionality.
Intersecting `indivisibleRoots i` with `positiveRelativeRoots i ν` is precisely
`indivisiblePositiveRoots i ν`. Reordering the quantifiers in the indivisibility
test and using `1 < n` if and only if `2 ≤ n` identifies it with
`reducedPositiveRelativeRoots i ν`. Divisibility is within the actual relative
root set, not primitivity in the character lattice. No restriction to reduced
systems or positive rank occurs.

The provenance is internal composition of the named published tangent-image,
action-weight-support and root definitions. The unchanged aggregate and its
Markdown describe its relation to Renard V.3.4 and V.3.12 and the explicit
extension from the source's local-field setting to arbitrary fields. This
module does not prove the fourth equality, comparing indecomposability in the
indivisible positive roots with indecomposability in all positive roots, and
does not prove the full aggregate or the separate root-system structural
statements.
