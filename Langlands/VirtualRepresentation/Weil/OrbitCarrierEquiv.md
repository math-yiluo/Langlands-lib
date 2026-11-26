# Changing the carrier universe of unramified-twist orbits

For a topological group with a continuous degree map to \(\mathbb Z\),
`Langlands.VirtualRepresentation.Weil.unramifiedOrbitCarrierEquiv`
identifies the unramified-twist orbit spaces of continuous irreducible
complex classes at independent representation carrier universes.
The group and degree map are fixed.

The proof applies `continuousIrreducibleCarrierEquiv` in every positive
rank. The resulting equivalence of the disjoint unions commutes with
every continuous character twist and in particular with the characters
obtained from the given degree map. Equivariance and injectivity show
that two classes are in the same orbit exactly when their images are.
The orbit equivalence follows by `Quotient.congr`. Its representative
formula sends the orbit of a class to the orbit of its image in the
same rank.
[Representation carrier equivalence](../../Weil/Representation/ContinuousIrreducibleCarrierEquiv.md)

This is a derived carrier comparison for the orbit construction in
`Langlands.VirtualRepresentation.Weil.Twist`. For the local Weil group
the action is the one in Henniart (1988), `henniart-1988-numerical`,
SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§§1.2–1.3, p. 498.
[Twist action](Twist.md)
