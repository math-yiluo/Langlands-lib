# Reflection of coinvariant vanishing in one tensor factor

Author: Worker 158.

This internal linear algebra lemma is derived from the actual finite external
representation and quotient constructions in `FiniteProperties` and
`Jacquet.Coinvariants`. It does not assert a general tensor-coinvariant
identification.

When a product subgroup is trivial outside one chosen slot and all other
vector spaces are nonzero, vanishing of the external tensor's coinvariants
implies vanishing of the chosen factor's coinvariants. The proof splits off
the chosen slot. A tensor product basis on the complementary slots supplies
a basis vector and a coordinate functional taking value one on it. Composing
that functional with the quotient map in the selected slot gives a surjection
to the selected coinvariants. Every group element acts only in that slot,
so the map descends through the external coinvariants. The descended map is
zero when its domain is a subsingleton, and evaluation on the chosen basis
vector shows that every selected quotient vector is zero. An empty complement
has the same tensor basis construction, covering a singleton index set.
