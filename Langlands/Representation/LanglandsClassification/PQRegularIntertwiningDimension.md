# The dimension consequence of regularity and the identity support piece

Author: Worker 135. This internal algebraic construction uses the published
normalized induction, Jacquet functor and identity support image for arbitrary
represented rational parabolics. It is an intermediate result for Task 5282;
it does not prove regularity of Langlands triplets.

For two parabolics with the same Levi scheme, a split component `a`, and a
`PQ`-regular smooth representation `sigma`,
`pqRegularIntertwiningRestrictionEquiv` constructs the linear equivalence
from `Hom_G(i_P sigma,i_Q sigma)` to the intertwining maps from the identity
support image in `r_Q i_P sigma` into `sigma`. It combines the proved
`leviFrobeniusReciprocity` with the comaximal-kernel restriction equivalence
from `Intertwining.ComaximalRestriction`. The centrality of the split component
supplies the central-image condition, and `IsPQRegular` is definitionally the
needed equality of kernel ideals.

`pqRegular_intertwining_finrank_eq_one` assumes in addition an equivariant
linear equivalence from that support image to `sigma`, admissibility and
irreducibility of `sigma`. Precomposition identifies its intertwiner space
with the endomorphisms of `sigma`; the published admissible Schur proof then
identifies it with `C`. Its complex finrank is one.

The universes of the local field and inducing representation remain independent.
These results impose no standardness, positivity or opposition assumption on
the two parabolics: the supplied regularity and support-image equivalence are
the exact premises used. They do not construct the support-image equivalence
or prove regularity. Their provenance is an internal assembly of published
constructions and the proved Frobenius and Schur results.
