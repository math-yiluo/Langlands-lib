# Actual fixed relative root-centralizer profiles

This internal construction selects a fixed integer-coordinate cocharacter
from an actual geometric identity-component fibre and controls its actual
relative centralizer. It does not assume reductivity for the selection,
self-centralizer inheritance or surviving-root dependence statements.

`mem_geometricSelfCentralizingTorusLocus_centralizer` proves that a supplied
closed relative standard torus remains self-centralizing in the geometric
identity component of every actual relative fixed-cocharacter centralizer
where it is self-centralizing in the original ambient identity component.
Indeed, the zero character annihilates every cocharacter. The previously
constructed actual centralizer inclusion differential therefore identifies
its zero-weight space with the ambient zero-weight space. Their relative
zero-weight ranks are equal. The proved zero-weight-rank criterion for
self-centralization then transfers the ambient condition to the centralizer.
The actual torus map into the centralizer is closed because its composite
with the closed centralizer inclusion is the original closed torus map.

For a specified actual geometric root, `rootCentralizerVector` takes the
integer coordinates of the existing generic cocharacter in that actual
geometric identity component. This cocharacter annihilates the specified
root and no root independent from it. Its construction uses the finite
actual adjoint root support of the smooth affine fibre and the split-torus
lattice pairing; it does not use a reductive-group root system.

`exponentCocharacter_rootCentralizerVector` proves that the fixed-exponent
cocharacter with this integer vector recovers the exact original generic
cocharacter on the original geometric fibre. Consequently the same vector
can be extended over the original arbitrary affine base using the existing
`exponentCocharacter` construction, whose arbitrary-scheme base change
compatibility is already proved. `dot_rootCentralizerVector` identifies
annihilation with the exact integer dot-product equation.

`dependent_of_mem_geometricRootCentralizerExponentRoots` concerns the actual
relative centralizer of that extended fixed-exponent cocharacter. Its
original geometric identity component has only roots dependent with the
specified original root. The proof uses the actual all-test centralizer
comparison and the actual differential weight comparison from
`RelativeCocharacterCentralizer`: a surviving root is an ambient root with
zero integer pairing. Exact original-cocharacter recovery then applies the
generic-cocharacter annihilation property.

The final theorem
`mem_geometricRootCentralizerExponentRoots_iff_pair` takes two explicit
forward field inputs at the original geometric fibre: the negative of the
specified root is an actual root, and every actual root dependent with the
specified root equals it or its negative. It proves that the actual
centralizer's full original geometric root support consists exactly of
that pair. The forward implication uses the preceding dependence theorem;
the reverse implication uses the annihilation dot product and its negative.
This theorem does not prove those forward negation or reducedness inputs.
Actual surviving-weight dimensions can separately be read from the existing
`finrank_geometricCentralizerWeight` theorem.

The provenance is internal, combining the already implemented generic
cocharacter construction, integral coordinate equivalences, actual
centralizer weight and geometric identity-component comparisons, and the
self-centralization rank criterion. The base ring may be nonnoetherian and
nonreduced, and ambient fibres may be disconnected. Construction of the
initial relative torus, forward field root structure and reflection inputs,
and the final general openness theorem remain outstanding.
