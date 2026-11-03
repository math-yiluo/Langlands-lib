# Ordered products through represented subgroup inclusions

These internal lemmas transport the actual ordered multiplication map through a
represented subgroup. They apply to group schemes over any base scheme and any
finite index `Fin n`, including `n = 0`. Their provenance is the existing all-test
subgroup representation and categorical product constructions; no additional
literature result is used.

`SubgroupFunctor.IsRepresentedBy.comp` identifies the all-test image of a
represented subgroup under a represented inclusion with the composite inclusion.
The proof composes the two monomorphisms and expands the pointwise range and image
conditions in both directions.

`orderedMultiplication_comp` and `comp_orderedMultiplication` use the monoid
homomorphisms on scheme hom-sets induced by postcomposition and precomposition.
A homomorphism preserves the `List.ofFn` product without changing its index order.

`orderedMultiplication_factorHom` applies the first equality to the canonical
factorizations from `Rational.LeviFactorization` and their exact inclusion
identities. `orderedProductIso` applies `asIso` to the actual internal ordered
product map, using the explicit hypothesis that this map is an isomorphism.
`orderedProductIso_hom_comp` proves the exact ambient inclusion equation, and
`exists_orderedProductIso` packages the resulting witness. Its product
isomorphism hypothesis is explicit: this helper does not establish the source
semigroup product theorem or the Dynamic root product target.

The point-evaluation identity `comp_orderedMultiplication` is reused from
`OrderedProductPoints`; its `orderedPoints` and product-point equivalence
unfold to the same ordered list product.
