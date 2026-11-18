# The specified component and ordinary quotient of the canonical standard Levi

This derived adapter identifies two actual constructions used in the
positive-decay proof. It preserves the specified split component and its torus
map, rather than replacing it by another choice.

`standardComponentSchemeHom` is the given component-to-maximal-torus map followed
by the canonical maximal-torus map into the standard Levi scheme. Its composite
with the actual Levi inclusion is the original ambient component map. Any
witness of `IsCompatibleStandardSplitComponent` represents that same all-test
Levi subgroup. The unique isomorphism between its representative and the
canonical representative carries the witness's split component to this
specified map. Thus it is an actual split component of the canonical Levi.
The pointwise comparison with `standardComponentHom` is the literal inclusion
identity under `Standard.leviPointsEquiv`.

The existing normalized Jacquet functor uses localized coinvariants and the
inverse half modulus. Its published ordinary-coinvariant equivalence specializes
definitionally to the action normalized by the exact `standardRadicalModulus`
used by the target's constant term. Restricting the equivalence through the same
`standardComponentHom` proves equality of generalized-eigencharacter predicates.

This is internal infrastructure for the actual normalized Jacquet coefficients
and component exponents in Waldspurger I.6.2 and VI.2.1–VI.2.3, printed pp.249,
297–300 of *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), source `waldspurger-2003-plancherel`. It composes published
representative uniqueness, split-component isomorphism transport, canonical
point inclusion, and normalized ordinary-coinvariant comparison. The module
asserts no spectral bound or positive-decay estimate.
