# The derived group of the general linear group

This internal helper proves that the actual special-linear inclusion is a closed
subgroup and exhibits the full derived subgroup, over every field and for every
finite index type, including the empty type. It implements the second clause
of the published `GeneralLinearCenterDerivedStatement`.

The range of the inclusion on arbitrary test schemes consists of the points
whose matrix has determinant one. The matrix points equivalences identify this
range with the full kernel of the determinant character. Monicity follows
from injectivity of the determinant-one matrix inclusion, and the isomorphism
between these two representatives transports the kernel's closed immersion
to the actual special-linear inclusion. Determinant multiplicativity places
all commutators in this range.

For a nonempty index type, the published simple connectedness of the actual
special-linear group includes semisimplicity. The published theorem that every
semisimple field group is perfect therefore makes SL perfect. Functoriality of
the full derived subgroup carries every SL point into the derived subgroup of
GL. The reverse containment uses the closed commutator-containing SL inclusion.
For an empty index type every SL point is the identity, so it is perfect as
well. This derivation uses only published results and Mathlib matrix identities;
its inherited source provenance is Milne, *Algebraic Groups* (2017), Examples
6.22 and 12.47, as explained in the unchanged target statement's Markdown.
