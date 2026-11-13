# Transport of actual local rank-one index alternatives

Author: Worker 177.

This is an internal transport construction for the existing actual-index
interface and its five local rank-one alternatives. It does not assert local
admissibility or prove `LocalRankOneTitsIndexStatement`.

Let `K : Type u` be any field. Let `G`, `H`, and `J` be group schemes over
`Spec K` whose structure morphisms are affine and locally of finite type.
Let `d`, `e`, and `c` be actual `TitsIndexData` for these groups. A
`TitsIndexEquiv d e` compares the same absolute Galois group element by
element; it preserves all Cartan pairings and exactly the zero vertices.

The definitions `TitsIndexEquiv.refl`, `.symm`, and `.trans` give identity,
inverse, and composite comparisons. The inverse uses the inverse vertex
bijection. Its Cartan, zero-vertex, and star identities follow by applying
the original identities to inverse images. The composite combines the
vertex bijections and their three identities.

For `f : TitsIndexEquiv d e`, `distinguished_iff` takes complements in
`f.zero_iff`. If `b : d.Vertex ≃ Fin n` is a numbering of `d` by a matrix
`M` and a marked predicate, `isNumberingOf` gives the numbering
`f.vertices.symm.trans b` of `e` by the same matrix and predicate. The
Cartan part uses `f.cartan_eq`; the marking part uses
`distinguished_iff`. No Cartan entry or membership implication is dropped.

`starIsTrivial` transports triviality by surjectivity of the vertex
bijection and its equivariance for each Galois element. `starImagePair`
uses the same equivariance at inverse images to transport both global
choices for every Galois element and the element realizing the specified
nonidentity permutation. The permutation and its nonidentity proof are
unchanged; the choice of permutation remains outside the vertex
quantifier.

The five `hasRankOne...` lemmas combine these transports for the existing
inner-A, outer-A, C, outer-D4, and inner-D5 predicates, preserving each
natural-number parameter. `rankOneAlternatives` applies the corresponding
lemma to each disjunct of the exact enumeration conclusion. Applying any
of these lemmas to `f.symm` transports in the reverse direction as well.

These are consequences solely of the definitions in
`Reductive.TitsIndex` and `SimplyConnected.LocalRankOneTitsIndexStatement`;
no additional literature claim is used. They make the enumeration stable
under an explicit comparison, including comparisons between indices of
different groups over the same field. They construct neither such a
comparison between arbitrary choices nor an admissible index. No local
field instance, characteristic restriction, simply connected hypothesis,
classification statement, or Kneser–Tits result is a proof input.
