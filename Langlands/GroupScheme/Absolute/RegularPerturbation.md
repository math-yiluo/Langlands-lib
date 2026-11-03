# Integral regular directions and sign-preserving perturbations

Worker 1270. This internal prerequisite formalizes the elementary finite-lattice
argument used in regular cocharacter constructions. It does not assert root
finiteness or the geometric comparison between root signs and subgroup functors.

For a finite family of homomorphisms from an additive commutative group to the
integers, `IntegralPerturbation.bound` is one more than the largest absolute
value on the error direction. Every natural number at least this bound is
positive. At such a number `N`, the signs of the forms on `N • μ + η` are
lexicographically determined by the form on `μ` and then by its value on `η`.
The proof uses the fact that a nonzero integer has absolute value at least one.

`IntegralPerturbation.exists_regular` constructs a direction at which every
nonzero form of a finite family is nonzero. The proof inducts on the family.
When a new form vanishes on the previous direction, choose a direction on which
that form is nonzero and use it as the error term in a sufficiently large
multiple of the previous direction. Earlier nonzero values remain nonzero.

`regular_and_nonneg` proves that a regular error direction makes the perturbation
regular and that a nonnegative value on the perturbation implies a nonnegative
value on the main direction.

`IsSplitTorus.isPerfPair_latticePairing` transports the published perfect
pairing of a coordinate split torus through a splitting isomorphism.
Consequently every nonzero actual character induces a nonzero integral form
on the actual cocharacter lattice.
`IsSplitTorus.exists_regular_on_finite` applies the finite-family construction
to any finite set of nonzero characters. `exists_regularCocharacter` specializes
this result to the published actual roots, assuming their finiteness explicitly.

`exists_regularCocharacter_perturbation` applies the sign and regularity bounds
to the published `latticePairing` and `IsRegularCocharacter`. Its finite-root
hypothesis and its already regular error direction are explicit. The result
holds over every field and for an arbitrary affine ambient group scheme; it
uses no reductivity, maximality, characteristic, or perfectness assumption.

These are derived arithmetic and lattice consequences of the Library interfaces.
The motivating regular-cocharacter construction is discussed in Milne,
*Algebraic Groups* (2017), Proposition 21.29 and the proof of Theorem 25.1
(source `milne-2017-algebraic-groups`). The proofs here are the elementary
integer-bound arguments described above, and they prove no Borel or parabolic
classification statement.
