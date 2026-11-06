# Actual relative graphs and their base-change compatibility

Author: Worker 1656.

This internal construction relates the published fixed-base graph
correspondence to actual relative Hom evaluation and torus-subgroup
family evaluation. All schemes and group schemes are actual objects in
an arbitrary universe `u`.

The four product-projection lemmas compute the forward and inverse
projections of the existing `baseChangeTensorIso`. That isomorphism is
the inverse monoidal structure map of actual scheme pullback lifted to
group objects. The lemmas are the Cartesian monoidal projection
identities. They imply `baseChange_graphHom`: the actual product
comparison takes a pulled-back graph inclusion to the graph inclusion
of the pulled-back homomorphism. Its proof compares the two projections.

For a relative homomorphism `i : H_T ⟶ G_T`, `relativeGraphHom i` is its
actual graph inclusion into `H_T ×_T G_T`, followed by the inverse
product comparison into the specified direct pullback `(H ×_S G)_T`.
Its first projection is the identity and its second projection is `i`.
`relativeGraph i` is the actual range subgroup functor of this map,
using all schemes over `T`. If `G/S` is separated, the graph is closed:
the existing closed-graph theorem applies to `G_T`, and composition with
the comparison isomorphism preserves closedness. If `H/S` is a split
torus, its pullback is a relative torus, so this range is admissible for
the torus-subgroup moduli interface.

`familyHom_relativeGraphHom` proves compatibility of actual inclusions
with arbitrary parameter maps `a : T ⟶ M`. Pulling the graph family over
`M` to `T` and applying the ambient comparison equals the graph of
`HomScheme.evaluate a i`, precomposed with the source comparison
`Descent.pullbackComparison M.hom a.left T.hom (Over.w a) H`.
The proof postcomposes with the product comparison and checks the two
projections. Naturality of the ambient comparison gives the first;
the definition of actual Hom evaluation as `Descent.pullHom` gives the
second.

Finally, `evaluate_relativeGraphHom` applies invariance of an actual
range under precomposition by an isomorphism. It establishes literal
equality of the evaluated subgroup functor with the relative graph of
the evaluated homomorphism, on every test scheme. This is the needed
family-evaluation comparison. No moduli scheme, open isomorphism locus
or representability theorem is asserted.
