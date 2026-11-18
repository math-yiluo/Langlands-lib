# One-dimensional connected group varieties are commutative

Worker 244, Task 7632.

`Langlands.GroupScheme.oneDimensionalCommutative` proves
`Langlands.GroupScheme.OneDimensionalCommutativeStatement.{u}` in every
universe `u`. For any field `k`, the theorem gives `IsCommMonObj G.X` for a
connected affine group scheme `G` over `Spec k` that is smooth of relative
dimension one. The statement is imported from
[OneDimensionalCommutativeStatement](OneDimensionalCommutativeStatement.md).

## Implemented proof

Faithfully flat quasi-compact base change reflects commutativity by
`isCommMonObj_of_baseChange`. The map from the spectrum of the algebraic
closure has these properties by `fieldExtension_fpqc`. Affineness and
smoothness of relative dimension one are stable under base change, and
`connectedSpace_baseChange_of_smooth_affine` preserves connectedness here.

Over the algebraically closed field, the smooth connected underlying scheme
is irreducible and has topological Krull dimension one. Its Lie algebra has
dimension one by `Lie.dimension_eq_of_smoothOfRelativeDimension`. The
published `lowDimensionSolvable` theorem gives solvability of the group
scheme, and `isSolvableGroupScheme_iff_isSolvable_points` gives solvability
of its group of rational points.

Suppose two rational points `a` and `b` have a nontrivial commutator.
The map sending `x` to `⁅a, x⁆` comes from a scheme morphism. The
irreducible closure of its image contains the distinct locations of the unit
and of `⁅a, b⁆`. If this closure were proper, the closed singleton of the
unit, the closure, and the whole scheme would form a strict chain of
irreducible closed sets of length two. This contradicts the dimension bound.
The rational points map into the first derived subgroup, so their density in
the source makes the first derived subgroup dense in the ambient scheme.
The proof uses `LeviGluing.range_subset_closure_rationalPointImage` for
this passage to the closure.

The operation `pointClosureSubgroup` takes the rational points in the
Zariski closure of a subgroup of rational points. The lemma
`commutator_pointClosureSubgroup_le` puts the commutators of two such
closures in the closure of the corresponding commutator subgroup.
Together with idempotence of closure, this makes every term in the
derived series dense once the first term is dense. Solvability gives a
trivial term whose closure is the trivial subgroup, contradicting the
nontrivial commutator. Thus the rational points commute.

The product of the group scheme with itself is smooth, hence reduced.
The two multiplication maps, one with the factors transposed, agree on
all rational points of this product and hence agree as morphisms by
`hom_ext_rationalPoints`. This yields `IsCommMonObj` and completes the
descent to `k`.

## Source

J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Proposition 14.25 on printed p. 286 (PDF p. 302) is the target. The
implemented proof uses Corollary 17.27 on printed p. 360 (PDF p. 376)
through the published [low-dimensional solvability proof](../Absolute/LowDimensionSolvableProof.md).
The argument applying solvability through the closures of the derived
series is the proof given in this module.
