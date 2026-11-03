# Descendant-Levi transport under associated-Levi conjugation

This internal derived helper restricts the actual associated-Levi conjugation
to each literal descendant standard Levi. It retains every actual normalizer
lift of the specified longest representative and uses inverse conjugation by
that same element on rational points.

For `J' = associatedSubset cs J` and `K : Finset J'`, the target descendant is
`leviIndex J (associatedFinsetEquiv cs J K)`. The first theorem proves that
its actual character set is the image of the source descendant's character
set under the actual longest Weyl action. Positivity follows from
`positiveSimpleSet_longestRep`, the literal inclusion `leviIndex_subset` and
`RootLengthComparison`. `PositiveSimpleReflectionComparison` identifies the
actual character action with the simple-reflection index transport. The
published `simpleImage_associatedFinsetEquiv` then gives the exact index.

`associatedDescendantLevi_map_conj` derives the actual ambient subgroup image
from `StandardLeviConjugationStatement`, through the published
`levi_map_conj_of_character_image`. The actual normalizer/full-centralizer
comparison changes only which quotient action is written; the supplied lift
and its rational point remain fixed.

`associatedLeviConjugationEquiv_descendant_mem` is the exact membership iff
needed to restrict the target's `associatedLeviConjugationEquiv` to the
literal `subgroupOf` descendant families. `associatedRestrictedLeviEquiv`
constructs that continuous group equivalence. Its evaluation theorem gives
`x ↦ n⁻¹ * x * n` on underlying rational points. All subgroup types and their
topologies are the actual ones; no representation comparison is a premise.
The root-set theorem works over any field with the displayed affine and
monomorphism instances, root and Weyl finiteness, and actual root-sign
comparisons. `associatedDescendantLevi_map_conj` additionally requires
`G` to be connected reductive, `i` to be a maximal split torus, `ν` to be a
generic cocharacter, and the named `StandardLeviConjugationStatement`.
The membership theorem and restricted equivalence retain all of these
hypotheses and additionally use the same intrinsic minimality and
associated-subset inputs as the published ambient equivalence and a
topological group structure on the rational points. The named standard-Levi
assertion is conditional on the three structural properties; it does not
supply them for the current objects. The canonical point topology and
finite-root instance of the full rational target are specializations.

This pair proves the descendant-Levi compatibility only. The corresponding
restricted parabolic and unipotent compatibilities, geometric expansion and
normalized representation identities remain obligations of the whole Jacquet
target. It does not change or prove that target.

Provenance is an internal consequence of the published actual associated-Levi
adapter and finite-subset equivalence. Aubert 1995 Theorem 1.7(2), equation
(1.9) and its final longest-representative reduction (printed pp.2181–2183)
motivate these exact subgroup indices. The implemented proof follows the
explicit root-set and subgroup-image calculation described above.
