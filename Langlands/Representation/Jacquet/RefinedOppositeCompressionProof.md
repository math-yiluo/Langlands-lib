# Proof of product opposite compression laws

This module proves the exact published proposition
`Langlands.Jacquet.RefinedOppositeCompressionStatement.{uF,uV}`.
The theorem `refinedOppositeCompression` preserves arbitrary smooth complex
representations of the outer product Levi, independent field/carrier universes,
and all natural ranks including zero. No admissibility or finite-dimensionality
assumption is used.

The proof adapts the published finite-orbit method of
`Jacquet.BlockCompressionProof` to the product opposite radical. The private
averaging helper identifies the orbits of a vector and its translate by an
element of the compact open subgroup, giving right-translation invariance.

For each element of the product compact open subgroup, choose its component
lower-Levi-upper factorizations. Combine each family of factors into an actual
product-group element. Component subgroup membership proves membership in the
actual product compact open and product lower radical. The inverse block scalar
commutes with the product Levi and conjugates the upper factors into the compact
open subgroup in the direction needed to fix the shifted vector. Thus its
compact-group orbit reduces to lower-radical translates.

For multiplicativity, use the published constant-orbit-value averaging lemma
on the inner compact average. The lower contraction containment puts the
conjugated lower translate inside the outer compact open, so right-translation
invariance removes it. Commutativity of the block-scalar tuples identifies
the product of the inverse scalars with the inverse scalar of their product.

For quotient compatibility, every lower translate has the same actual
coinvariant class by `mk_apply_subgroup`. Apply the same constant-orbit-value
lemma to the actual quotient map. All constructions are those in the target,
and only smoothness of the arbitrary product representation is used. This proof
does not establish canonical-lift bijectivity, admissibility or generic comparison.
