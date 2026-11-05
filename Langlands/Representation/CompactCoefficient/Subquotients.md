# Compact coefficients on arbitrary actual subquotients

Worker 491 gives an internal construction of the compact-restriction object
property and proves its permanence under all actual smooth subquotients.
The inputs are the existing compact smooth-dual coefficient predicate, actual
subgroup restriction, and the published extension theorem for smooth
functionals. No new external representation-theoretic result is assumed.

For an equivariant surjection, pull a smooth target functional back to the
source. The intertwining identity identifies its source coefficient with the
original target coefficient after choosing a preimage of the vector.
`HasCompactSmoothDualCoefficients.of_surjective` therefore needs no smoothness
assumption on the original representations, no topological-group assumption,
and no compact-open hypothesis.

For an injection of two smooth complex representations, assume that compact
open subgroups are cofinal among open subgroups of the topological group.
The published smooth-contragredient surjectivity theorem extends each smooth
functional on the source to a smooth functional on the target.
The same coefficient identity proves
`HasCompactSmoothDualCoefficients.of_injective`. The two representation
carrier universes are independent, as is the group universe.

An actual smooth subquotient has the published presentation by an intermediate
smooth object that injects into the ambient object and surjects onto the
subquotient. Applying the injection and surjection laws proves
`SmoothRep.hasCompactSmoothDualCoefficients_of_isSubquotient`. This tests
arbitrary actual subquotients and does not require irreducibility, admissibility,
finite length or finite dimension.

`SmoothRep.compactRestrictionProperty N` is the object property that the
actual restriction to the subgroup `N` has compact smooth-dual coefficients.
It does not assert compactness of the subgroup. Its isomorphism law comes
from the actual restriction functor and coefficient transport along an
actual representation equivalence. If compact open subgroups of `N` are
cofinal, actual restriction preserves subquotients and the preceding permanence
law shows that this property is closed under every actual ambient subquotient.
Consequently it is equivalent to the property that every such subquotient has
compact restriction; the converse uses the object as its own subquotient.
Normality of `N` is not required.

The motivation is the first decomposition of Renard VI.3.5 (French edition
dated 9 July 2026, printed pp.146–147 / PDF pp.152–153). This internal permanence
argument supplies algebra needed to pass from a compact restricted summand
to an all-subquotient factor. It does not construct invariant complements,
prove compact-restriction equivalence with proper-standard cuspidality,
or prove the whole-category splitting. The implemented proof follows the
functional-extension and actual-map argument described above.
