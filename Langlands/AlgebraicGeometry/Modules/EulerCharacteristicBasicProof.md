# Proofs of basic identities for actual Euler characteristics

`DerivedSections.eulerCharacteristicBasic` proves the full published
`EulerCharacteristicBasicStatement`. The module also exposes the cutoff,
finite-cohomology transport and isomorphism-invariance lemmas separately.

For a vanishing bound `N`, categorical zero implies that the underlying
cohomology vector space is a subsingleton and thus has dimension zero in each
degree at least `N`. Therefore the alternating summand has support in
`Finset.range N`, and Mathlib's `finsum_eq_sum_of_support_subset` turns the
actual Euler definition into that finite sum.

For an actual sheaf isomorphism, each actual relative cohomology functor
produces an isomorphism of vector spaces. Its linear equivalence transports
finite-dimensionality, while the categorical isomorphism transports vanishing
with the same bound. Applying the same argument to the inverse gives the
finite-cohomology equivalence. The linear equivalence preserves finrank, so
pointwise equality of the summands gives equality of their `finsum` values.

Finally, the all-zero and positive-degree-zero formulas follow from the cutoff
identity at bounds zero and one. No long exact sequence, Hilbert polynomial,
intersection pairing or finite-flat numerical degree assertion is used.
