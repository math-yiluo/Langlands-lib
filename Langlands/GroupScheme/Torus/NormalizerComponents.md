# Maximal-torus normalizers detect connectedness

This is an internal consequence of published maximal-torus conjugacy,
functoriality of actual identity components, and closed subgroup containment
detected on algebraically closed field points. It supplies the final
group-theoretic step in a connected-fibre argument; it does not establish the
required normalizer containment in a family.

Let \(k\) be algebraically closed, \(G\) a smooth affine \(k\)-group, and
\(t:T\to G^0\) a maximal torus of the actual identity component. The ambient
group \(G\) need not be connected or reductive.

For every \(g\in G(k)\), `exists_identityPoint_mul_mem_normalizer` constructs
an identity-component point \(p\in G^0(k)\) such that \(p g\) normalizes the
ambient torus \(T\to G\). Conjugation by \(g\) induces an automorphism of
\(G^0\), by functoriality of the identity component. The torus obtained from
\(t\) by this automorphism is maximal. The published conjugacy theorem applied
inside the smooth connected affine group \(G^0\) supplies \(p\) and an actual
torus automorphism. Their composition equation proves that \(p g\) lies in the
full normalizer on every refinement of the base test scheme.

`normalizerComponentRepresentative` chooses the resulting actual normalizer
point. The lemma `normalizerComponentRepresentative_mul_inv` shows that its
product with \(g^{-1}\) factors through \(G^0\), so it belongs to the same
component as \(g\). These are group-scheme sections and the published
normalizer-points subgroup, not a supplied abstract component action.

Suppose that every rational point in this full normalizer factors through the
identity-component inclusion. Then \(p g\) and \(p\) both lie in the subgroup
\(G^0(k)\), so \(g\) does too. This is
`mem_identityComponent_of_normalizerPoints_le`.
The reducedness of the smooth ambient group allows the published
algebraically closed point-containment theorem to extend this to containment
on all scheme tests. Uniqueness of factorization through the closed
identity-component inclusion constructs
`identityComponentIsoOfNormalizerPoints : G^0 ≅ G`. Its forward homomorphism
is the actual inclusion, as recorded by the corresponding `_hom` lemma.
Finally `connectedSpace_of_normalizerPoints_le_identityComponent` transports
connectedness along this isomorphism.

All declarations have arbitrary universe \(u\). The explicit normalizer
containment remains a hypothesis of the isomorphism and connectedness
conclusions. No generic-special Weyl-order comparison, theorem on families,
or unconditional reductive monomorphism closedness is asserted here.
