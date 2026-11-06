# Base-change isomorphisms classify natural local isomorphisms

This internal construction works for every base scheme `S : Scheme.{u}`, actual
group schemes `G` and `H` over `S`, and arbitrary `U : Over S`, with arbitrary
universe `u`. It imposes no covering, field, or reductivity hypothesis.

`LocalGroupIso.baseChangeIsoEquiv` identifies actual isomorphisms between the
pullbacks of `G` and `H` to `U` with the existing natural local multiplicative
equivalences indexed by every point of `U` on every relative test scheme. Its
forward map is `ofBaseChangeIso`; its inverse is `toBaseChangeIso`.

The proof first establishes extensionality of local isomorphisms by all their
point values. Starting from a local family, evaluate its recovered isomorphism
on the test lifted to the cover. The projected-point formula for recovery and
naturality along the identity-underlying comparison with the original test
recover precisely the original local value. Starting from an actual
isomorphism, its projected point values agree with those required by recovery:
the lifted source point has the same two pullback projections as the original
point. Uniqueness of the recovered isomorphism then proves the other inverse
identity. These identities supply the two inverse laws of the equivalence.

The provenance is internal: the argument uses the two existing pointwise
constructors, their projected-point and uniqueness formulas, pullback
extensionality, and naturality on all relative tests. This classification does
not construct a quasi-split model, adjoint quotient, finite field extension,
initial local isomorphism, or discrepancy cocycle. Those remain obligations of
the quasi-split inner-form existence theorem.
