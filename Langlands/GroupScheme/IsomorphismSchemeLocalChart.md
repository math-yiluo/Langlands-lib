# Local representatives of the full Isom presheaf

This internal construction specializes the published general
`LocalRepresentation.chartProductIso` to the all-test Isom presheaf. Its
inputs are the `LocalGroupIso` base-change equivalence and a supplied
`GroupIsomorphismScheme`; it assumes the local representative exists.

For an arbitrary base morphism `b : S' ⟶ S`, restriction along `Over.map b`
identifies the original-base Isom presheaf with the Isom presheaf of the
base-changed groups. The inverse family transport commutes with every
new-base parameter refinement, as follows by applying the family
base-change equivalence and its inverse laws.

Suppose `I` represents the full Isom functor of the two groups over `S'`.
The local representing equivalence, followed by the inverse base-change
presheaf isomorphism, represents the restriction of the original Isom
presheaf. Applying the published general chart construction gives
`localChartIso`: the actual local parameter, viewed as a scheme over `S`,
represents the product of the original Isom presheaf and the functor of
points of `S'` over `S`.

The first projection is `localChart`, whose evaluation at every
original-base parameter point is refinement of the local universal family
transported back to the original base. This formula follows by evaluating
the representation at the identity and simplifying identity refinement.
The second projection is exactly the actual parameter projection to `S'`.
The general chart theorem supplies the product universal property on all
original-base scheme tests, including those whose new-base structure is
specified by the parameter point.

All bases, morphisms and group schemes are unrestricted. No geometric
existence or effective descent is asserted here. Etale local
isomorphisms, local geometric representability, and effective descent of
the resulting charts remain separate obligations.
