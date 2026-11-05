# Coalgebras embedded in monomial coalgebras

Author: Worker 1467.

This is an internal derived linear-algebra helper. For a field `k`, the
coalgebra structure on `AddMonoidAlgebra k M` has diagonal monomial
comultiplication. No group or monoid structure on `M` is needed.

`coefficientContraction m` applies the coefficient functional at `m` to the
second tensor factor. Applied to a comultiplication it extracts exactly the
`m`-monomial component. A coalgebra map therefore has each such component
in its linear range; over a field every nonzero component can be rescaled
to the monomial with coefficient one.

An injective coalgebra map reflects group-like elements: it preserves the
counit, and injectivity of its tensor square reflects the comultiplication
equality. The finite monomial expansion of each image then proves that the
source coalgebra is spanned by its own group-like elements. This is the
content of `span_isGroupLikeElem_of_injective`.

The proof uses the published monomial coalgebra structure and tensor
injectivity for vector spaces. It requires no finite-dimensionality,
smoothness, characteristic restriction, or character classification.
