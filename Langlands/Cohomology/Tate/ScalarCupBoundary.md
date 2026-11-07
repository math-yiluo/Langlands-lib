# Scalar cup products and connecting maps

Let `R` be a commutative ring and `G` a finite group, with the common universe
parameter used by the Library's actual representations and Tate cohomology.
Worker 1736 constructs the scalar-multiplication map from a tensor coefficient
sequence to its original sequence. Naturality of the actual Tate connecting
map and the published first-variable tensor cup boundary law show that scalar
cup commutes with the first connecting map. The explicit-degree variant records
the equality used to identify the successor degree.

The degree-zero scalar unit class is the class of the invariant scalar one.
The implemented proof that cup by this class is the identity uses the
published invariant-vector normalization and the identity obtained by composing
tensoring with one and scalar multiplication.

The construction `scalarDoubleBoundaryClass` takes two actual short exact rows
`0 → A → B → Q → 0` and `0 → Q → P → R → 0`, where `R` denotes the trivial
scalar representation. It applies the second row's degree-zero Tate boundary
to the class of one, then the first row's degree-one boundary, and finally the
published comparison from Tate degree two to ordinary group cohomology.

When both rows split after forgetting the group action,
`scalarH2Cup_doubleBoundary` identifies cup on the left by this ordinary class
with the composite of the two Tate boundaries in every integer degree `n`.
The target is degree `n + 2`; the formula explicitly transports degrees to
match the Library's scalar cup convention. The proof applies the
first-variable scalar boundary formula twice, uses scalar cup by one, and
then cancels the degree transports by the boundary naturality squares.

If `P` has zero Tate cohomology in every degree and these cup maps are
bijective in every degree, `scalarDoubleBoundary_delta_isIso` proves that all
first-row boundaries are isomorphisms. Indeed, the second-row boundaries are
isomorphisms by the Tate long exact sequence, so they can be canceled from
the bijective composites. The independent helper `tate_middle_isZero` uses
surjectivity of the preceding boundary and injectivity of the following one
to kill both maps adjacent to the first middle term. Exactness then makes
that middle Tate group zero. This gives
`scalarDoubleBoundary_middle_isZero` for `B` in every integer degree.

This is an internal consequence of the Library's actual Tate cup, boundary
and exactness constructions. Worker 1607 contributed the splitting-module
strategy and two-row interface; Worker 1736 implemented these constructions
and proofs. No external source assertion or additional axiom is introduced.
The module does not assert that any particular extension cocycle equals the
double-boundary class, or that an extension transfer has already been
identified with a norm. Those are separate inputs to the intended application.
