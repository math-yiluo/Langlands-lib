# Common actual subquotients from matching composition factors

Author: Worker 120.

This internal statement isolates an elementary bridge used in the proof of
`CuspidalInductionAssociationTheorem`. It combines the published definitions in
`Filtration.ObjectDefinitions` and `Category.Subquotients`; it is not a new
translation of a literature theorem.

`HaveCommonIrreducibleSubquotient A B` means that each smooth representation has
an actual invariant subspace and an actual invariant subspace of that subspace,
such that the first resulting quotient is irreducible and the two resulting
representations are equivariantly linearly equivalent. This is the same
existential condition used in the cuspidal-induction association statement.
The two ambient carrier universes are independent, as are the group and field
universes. No categorical isomorphism between different carrier universes is
asserted.

`SameFactorsCommonSubquotientStatement` states that, over any field and
topological group, a nonzero smooth representation and another smooth
representation with matching actual Jordan–Hölder factors have such a common
irreducible subquotient. Only the first representation is explicitly assumed
nonzero. The published factor-matching predicate supplies finite composition
series, including the irreducibility of every factor and an equivalence of
each matched pair. No separate finite-dimensionality or finite-length
assumption is imposed.

The nonzero hypothesis excludes empty composition series of zero
representations. The intended elementary proof selects a factor from the
nonempty composition series and realizes both graded objects as the actual
subquotients specified above. This file states the claim and does not prove it.
