# The complex Langlands quotient in the original induction order

`ComplexOrderFactorizationStatement` concerns a list of complex characters of
length `n` and its stable sort by decreasing real part of the exponent. It
asserts that a nonzero intertwiner from the sorted standard module to the
standard module of the reversed sorted list factors through the module of the
original list. The modules are the `U(n)`-finite vectors with the compact and
complexified Lie actions.

The proof reverses the stable decreasing sort to reach the original list by
strict swaps. It continues by a stable increasing sort. Converting the two
paths to `StrictSwapChain` gives the composite, whose nonvanishing follows
from the product chart integral. The increasing list and the reversal of
the decreasing list are sorted permutations of one another.
`ComplexTransposePairingReduction.injectiveIntertwiner_sorted_perm` gives an
injective comparison across the equal-exponent swaps, which preserves
nonvanishing of the composite.

`complexOrderedQuotient_subquotient` takes the quotient by the largest proper
stable subspace of the sorted module. The reverse-intertwiner kernel criterion
identifies that subspace with the kernel of the composite. The quotient map
therefore descends to a surjective equivariant map on the image of the first
intertwiner inside the original standard module.

This is a local ingredient for the archimedean constituent step in Getz and
Hahn, *An Introduction to Automorphic Representations* (2024), Theorem 10.6.4,
printed p. 286 (PDF p. 298). The decreasing order and the irreducible quotient
are those in Knapp, *Local Langlands correspondence: the archimedean case*
(1994), (4.3) and Theorem 4(a), printed p. 405 (PDF p. 415). The factorization
is implemented using the Library's strict swap integrals and its unlinked
comparison of equal-exponent characters.
