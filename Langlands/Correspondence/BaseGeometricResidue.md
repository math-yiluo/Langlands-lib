# Geometric residue normalization of the actual base candidate

This internal consequence gives full geometric normalization of the actual
base candidate of a supplied normalized common-closure reciprocity family.
The prime, field and all supplied finite-extension topological data remain
arbitrary. No common-closure family is constructed.

The spectral integer ring used by the absolute residue construction equals
the integer ring of any supplied topological datum on the finite extension.
The proof identifies both by integrality. The canonical base integer ring
is integral over the p-adic integers, so integrality over either base ring
is equivalent.

Naturality of the constructed absolute residue action under finite Galois
restriction identifies inverse geometric Frobenius with the residue-cardinality
power map. The spectral and supplied integer-ring comparison, followed by the
existing supplied residue congruence theorem, turns this into the exact
discrete-valuation inequality in `GeometricProfiniteReciprocityRelation`.

For a specified actual local Weil candidate, a uniformizer's inverse image
has degree one by `GeometricOrderRelation`. The constructed local Weil
residue-action theorem gives geometric Frobenius at that degree. Finite
restriction of the candidate recovers actual Galois restriction, yielding
the required congruence. Thus `LocalReciprocityCandidateRelation` implies
the full `IsGeometricReciprocity`; the reverse implication is its two
corresponding conjuncts.

`BaseGeometricReciprocityStatement`, with its included proof, applies this
to `baseReciprocityCandidate` using the finite norm-residue laws in
`BaseNormResidue`. The final theorem transfers full geometric reciprocity
to every base candidate satisfying `IsBaseReciprocity` with the same
supplied normalized family.

The family and its normalized coherence remain explicit premises. This unit
does not prove their existence or the closed supercuspidal correspondence.
