# Centre-moving norm-one automorphisms and opposite algebras

`NormOneCenterAutomorphismOppositeStatement` is an internal structural proof
target. For every field `K` and finite-dimensional central simple `K`-algebra `A`,
it asserts that an automorphism of the actual reduced-norm-one group scheme
which fails to fix its full scheme-theoretic centre implies the existence of a
`K`-algebra equivalence from `A` to its opposite algebra.

The norm-one group is `CentralSimpleUnits.normOne K A`, the actual kernel of the
unconditional reduced norm. The automorphism is an isomorphism in the category of
group schemes over `Spec K`. The premise uses `AutomorphismFixesCenter`, so it
tests all points of the full centre on every test scheme, including nonreduced
test schemes. The conclusion is a scalar-fixing algebra anti-equivalence. It
imposes no involutivity condition on its product-reversing underlying map.
There are no restrictions on the field, characteristic, reduced degree or
universe parameter, and no division-ring premise.

This target isolates a substantial missing prerequisite for the local rank-one
Tits-index proof. An actual central division norm-one presentation of an
anisotropic kernel and an automorphism moving its centre would then supply the
algebra anti-equivalence needed by the independent local division-algebra degree
argument. Constructing that automorphism from the relative Weyl symmetry remains
a separate obligation.

The provenance is internal: this is the precise structural implication requested
by that proof route, expressed using the existing actual norm-one group and full
centre interfaces. It is not attributed here to a literature theorem. This file
defines the proposition and does not prove it, construct the required
automorphism, or establish any local Tits-index exclusion.
