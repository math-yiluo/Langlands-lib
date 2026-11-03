# Canonical cocharacters and reductions at standard-parabolic endpoints

Author: Worker 74.

This module proves internal consequences of the published intersection definitions in
`Rational.StandardParabolic`. It uses the actual subgroup functors on every test scheme,
and leaves the imported statement declarations unchanged.

`standardEmptyCocharacter i ν` constructs an element of the subtype of cocharacters
standard for the empty index. Its underlying cocharacter is `ν`: every simple root is
positive by definition. `standardFullCocharacter i ν` constructs an element of the
corresponding subtype for the full simple-root index; its underlying cocharacter is zero.
Their value lemmas are definitional equalities. The construction needs only an affine
group scheme over a field, a commutative group scheme and its homomorphism to the group.
These witnesses give inclusions of the empty parabolic and Levi in the dynamic groups of `ν`.
If that dynamic centralizer equals the whole-torus centralizer, the inclusion and the
published reverse inclusion identify the empty-index Levi.

The zero cocharacter stays trivial after composition with `i`. For a separated group
scheme, uniqueness of orbit limits implies that a cocharacter whose dynamic centralizer
is the whole group has trivial dynamic unipotent subgroup. Consequently the full-index
standard unipotent is trivial for every affine group scheme; reductivity, maximality and
genericity are not needed for this clause.

The final theorem is an explicit conditional reduction from `GenericCentralizerStatement`
and `StandardCocharacterStatement` to `StandardParabolicEndpointsStatement`, with all
three statements at universe `u`. The standard-cocharacter comparisons applied to the two
witnesses give the empty parabolic and the full parabolic and Levi. This reduction does
not prove either structural premise and is not an unconditional proof of the endpoint
target. Its provenance is the published definitions and uniqueness of separated orbit
extensions, rather than an additional assertion from the literature.
