# Whole target Boolean interval

Author: Worker 194.

This internal combinatorial prerequisite identifies the source cut sets where
the Weyl intersection is the whole fixed target Weyl group. It specializes the
existing signed Boolean interval contraction to degrees below the target cut
count. The construction allows every natural rank, including zero, and an
arbitrary complex coefficient module in an independent universe.

Fix a target block shape `C` and a coordinate permutation `v`. In the support
application `v` is the inverse of the support permutation. The source shape is
`B`, so the representative convention in this module is
`IsMinimalRepresentative C B v`. The whole-target condition is

```text
blockWeyl C ∩ conjugate-pullback-v (blockWeyl B) = blockWeyl C.
```

`wholeTarget_iff_interval` proves that this condition together with minimality
is equivalent to three explicit conditions: `v` increases on every block of
`C`; every uncut edge of `C` maps to adjacent increasing coordinates; and
`B.cuts` belongs to a Boolean interval. The required cuts are the descents of
`v.symm`. The allowed cuts are the complement of `blockEdgeImages C v`,
the image edges of uncut edges of `C`. These statements use the actual block
Weyl subgroups and their conjugation pullback.

The proof first applies the published type-A theorem `admissible_iff` with both
its source and intersection shapes equal to `C`. At an uncut edge of `C`,
the last admissibility equivalence has false left side. Its right side must
therefore have a counterexample, which gives an actual adjacent image edge.
This proves `blockEdgeAdjacent_of_admissible`. When the fixed source order and
adjacency conditions hold, admissibility says precisely that all inverse
descents are included and all image edges are excluded. This gives
`admissible_iff_interval` and its unconditional version
`admissible_whole_iff`.

Adjacency also implies that an inverse descent cannot be an image edge:
the inverse images of its endpoints would be the increasing endpoints of an
uncut target edge. Thus `descents_subset_allowedCuts` proves that the interval
is nonempty. Sending each uncut target edge to its image gives a bijection
onto `blockEdgeImages`; injectivity follows from injectivity of `v` and of the
left-endpoint map. `blockEdgeImages_card` and finite complement cardinality
then give `allowedCuts_card`, equal to `C.length - 1`. The proof uses the
rank-zero-safe cut count and does not assume that `n` is positive.

`diagram C v M` is exactly the existing constant-coefficient Boolean interval
diagram, with the existing signed insertion differential. Under adjacency,
`exact_below_target` identifies its differential range with the next kernel
whenever the middle degree `k+1` is strictly below `C.length - 1`.
`injective_before_target` proves injectivity of the initial differential when
that target degree is positive. These results follow from the previously
proved Boolean contraction and the two cut-set bounds. Singleton-interval
homology in the target degree is retained.

The provenance is internal. The combinatorial proofs use the existing
`TypeASolomon.Admissible` characterization, finite-set bijections and cut counts;
the algebraic conclusions specialize `BooleanIntervalComplex`. This module
does not identify a genuine graded Jacquet coefficient with the constant
coefficient diagram. That coefficient comparison and its compatibility with
the actual differential remain separate prerequisites for signed effectivity.
