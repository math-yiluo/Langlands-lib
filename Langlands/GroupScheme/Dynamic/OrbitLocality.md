# Locality of actual orbit extensions on test schemes

Workers 3483 and 286. Internal helpers for arbitrary-base dynamic representability.

The product-chart helpers identify the pullback of a test scheme's open cover
along the first product projection with products of its charts. They also give
an equality criterion for morphisms from such a product. These are direct
consequences of the pullback universal property and scheme morphism gluing.

For a separated group scheme, `orbitExtension_compatible` compares two local
extensions by pulling them back to the product with the affine line. Their
underlying points agree; uniqueness of extensions then implies agreement after
evaluation along the common affine-line coordinate. The generic product gluing
lemma therefore glues the local extensions. The extension equation is detected
on the product cover with the multiplicative group.

The resulting `parabolic_isZariskiLocal` and `unipotent_isZariskiLocal` prove
Zariski locality of membership on every test scheme. For the unipotent functor,
evaluation at zero commutes with restriction, so the identity value is detected
on the original test cover. `centralizer_isZariskiLocal` detects the constant
orbit equation on the product cover and does not require separatedness.

Uniqueness comes from the published `AffineLine.hom_ext_of_unitInclusion`,
which is valid for nonreduced tests. These internal lemmas derive from the
published orbit-extension definitions, uniqueness theorem and scheme gluing;
they introduce no new source convention or field restriction.
