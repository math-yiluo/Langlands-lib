# The Levi graph cell on actual group-scheme rational points

This derived internal module specializes the word induction of
`SplitLeviGluingDensity` to the actual rational points of a group scheme `H`
over an arbitrary field `k : Type u`. Its index family has an independent
universe `v`. The rational points are morphisms over `Spec k` from the
identity `Spec k` object to `H.X`, with their actual group operation.

The local topology is `RationalZariski.topology H`, induced by the location of
a point in the underlying space of `H`. Left and right multiplication by a
fixed rational point are continuous: `exists_comp_eq_mul_left` and
`exists_comp_eq_mul_right` express each translation as postcomposition with
an actual scheme endomorphism, and `RationalZariski.continuous_comp` proves
its continuity. No continuity of multiplication on a product topology is
used. The theorem `closure_eq_rationalPointClosure` identifies this
topological closure with `rationalPointClosure H`, by the general
`closure_induced` theorem.

`generated_mul_mem_rationalPointClosure_tripleProduct` transfers the abstract
stability theorem to this intrinsic rational-point closure. The construction
`rationalTripleProductClosureAction` is the resulting action of the
abstractly generated subgroup on the rational-point closure of `V * T * U`,
given by left multiplication. Its identity and associativity laws are those
of the actual rational-point group.

`dense_rationalPointImage_tripleProduct` proves that the locations of the cell
are dense in the underlying scheme space if the locations of the generated
subgroup are dense there. For each point in that subgroup, the abstract
containment theorem places its location in the closure of the cell's
locations. Taking closures and using the supplied density proves the result.
The density assumption is about locations in the scheme, so no passage from
density merely within the rational points is asserted. Algebraic closedness,
finite type, smoothness, affineness and reductivity are not needed under this
explicit density assumption.

The normalization, distinct-index commutation, negative-factor abstract
generation and equal-index rank-one closure relations are all supplied
hypotheses. The group-scheme adapter constructs none of the factors and does
not derive these hypotheses or generated-location density from reductivity.
It does not prove `SplitCommonTorusLeviGluingStatement` or the main
`SplitCommonTorusIsomorphismStatement`.

The provenance is the abstract word-induction unit, which cites Milne,
*Algebraic Groups* (2017), Proposition 23.22, printed p.491 (PDF p.507), and its
official 2017 errata snapshot. This adapter is an internal derivation using
the Library's actual rational-point topology and closure interfaces, rather
than a separate source assertion.
