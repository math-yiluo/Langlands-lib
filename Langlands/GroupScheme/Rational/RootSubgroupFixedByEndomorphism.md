# Fixedness of actual roots and their opposite factor pairs

Author: Worker 1368.

This is internal derived content from the published actual-root subgroup,
normalizer-conjugation, opposite-pair transport, uniqueness and rational
nontriviality interfaces. It makes no new literature assertion.

`RelativeRoot.IsFixedBy i f a` says that the entire actual root subgroup
functor for `a` is contained in the subgroup fixed by the endomorphism `f`.
This quantifies over every test scheme, including nonaffine and nonreduced
tests. An endomorphism satisfying `i ≫ f = i` preserves each root functor:
the published `comp_mem_subgroup` transports membership to the torus map
`i ≫ f`, and that equality identifies the result with the original torus.

For monomorphic torus inclusion, a normalizer point fixed by `f` transports
fixedness from `a` to `weylAction i n a`. The proof conjugates an arbitrary
point of the latter subgroup back to the former using the published
normalizer equivalence. Constant pullbacks of `n` remain fixed, so applying
`f` to the conjugation equality proves the required equality on the original
arbitrary test scheme. This step does not require `f` to fix the torus.

Over an arbitrary field, for affine `G` and split `T`, suppose that `x` is a
nonidentity point of the actual `a`-root subgroup and is fixed by `f`, that
`a ≠ 0`, and that a normalizing opposite factor pair `p` is supplied. The
endomorphism must fix the torus. The published pair transport sends `p` to
another ordered pair for the same point `x`. The published uniqueness theorem
then makes both ordered factors fixed. Their three-factor product with `x`
is consequently a fixed actual normalizer point.

The published pair reflection theorem says that this normalizer sends `a`
to `-a`. If the entire `a`-root functor is fixed, the conjugation result above
therefore makes the entire negative-root functor fixed. The last theorem
assumes smooth `G`, actual root occurrence and `HasOppositeFactorPairs i`.
The unconditional rational nontriviality theorem provides the required
nonidentity root point, and the explicit existence premise provides its pair.

No opposite-pair existence is proved here. No reduced-root, perfect-field,
characteristic, semisimplicity or simple-connectedness restriction is used.
These results supply propagation steps toward pinned rigidity, not a proof
of its unconditional target.
