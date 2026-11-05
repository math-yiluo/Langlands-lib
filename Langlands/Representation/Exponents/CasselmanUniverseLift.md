# Arbitrary carrier universes in the strict Jacquet criterion

Author: Worker 1682.

This internal supporting module removes a carrier-universe restriction
when applying the published strict Jacquet sufficiency statement. It
retains that statement as an explicit hypothesis and does not prove it
or the full Casselman criterion.

An actual representation equivalence induces a linear equivalence of the
character-localized quotients for the trivial radical character. On a
quotient representative it maps the class of a vector to the class of its
image. This map intertwines the descended Levi actions, and it commutes
with the common inverse half Haar-modulus scalar. It is therefore an
equivalence of the actual normalized Jacquet representations. The
published full-center exponent invariance under representation
equivalence applies, without a carrier-universe equality requirement.

For a representation with carrier universe `v` and field universe `u`,
the proof uses `SmoothRep.universeLift` to place its carrier in
`max (u + 1) v`, the universe required by
`RationalStrictJacquetSquareIntegrabilityStatement`. The published
universe-lift equivalence preserves admissibility and carries the actual
unitary central character. The normalized Jacquet equivalence transfers
every full-center exponent back to the original representation, so the
original pointwise strict bound supplies the lifted strict bound.

The supplied strict sufficiency theorem now gives square integrability
of the lift. The existing coefficient-based square-integrability
transport along a representation equivalence returns the conclusion
for the original representation and the same central-quotient Haar
measure. No irreducibility or finite-length condition is used.

This is an internal deduction from the published constructions and
equivalence laws. The actual standard-cocharacter and radical closedness
premises and the strict sufficiency proposition remain supplied.
