# Split series on actual finite-Galois descended radicals

This internal construction attaches the conditional finite-Galois split-series
descent result to the existing actual radical and torus-quotient descent data.
Every result explicitly assumes
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}`. It does not prove
that structural statement or the rational maximal-torus conjugacy theorem.
Both fields have arbitrary universe `u`, and the extension is finite Galois.
All characteristics, finite fields and imperfect fields are retained.

`IsUnipotentRadical.isSplitUnipotent_of_finiteGalois` starts with an existing
represented ground-field radical in an affine ambient group. Its unchanged
radical predicate supplies smoothness, connectedness and actual
representation-theoretic unipotence. Closedness of its inclusion supplies
affineness of the radical. If its base change to the given extension has a
represented split series, the conditional finite-Galois descent theorem
therefore gives a represented split series over the base field. No smoothness
or connectedness of the ambient group is required for this lemma.

`IsUnipotentRadical.finiteGaloisSplitRadical` takes an actual represented radical
over the extension, assumed split, in the base change of an affine group.
The existing `finiteGaloisRadical` supplies a ground-field radical, its
inclusion, a source isomorphism recovering the given extension-field radical,
and the exact commuting inclusion equation. Split series transport through
the inverse of that source isomorphism. The preceding lemma descends the
transported series. The same ground-field inclusion then satisfies both
`IsUnipotentRadical` and `IsSplitUnipotentRadical`; greatestness among all
smooth connected unipotent normal closed subgroups implies greatestness among
the split ones. The constructor retains the original source comparison and
inclusion equation.

`FiniteGaloisTorusQuotientDescent.isSplitUnipotent` applies this reasoning to
the radical already stored in a supplied torus-quotient descent. That data
already proves the geometric radical predicate over the ground field and its
algebraic closure. Its stored source comparison transports the given
extension-field split series, and the ground-field part of the radical
predicate discharges the descent hypotheses. This attaches splitness to the
same radical without changing the stored quotient or projection.

`finiteGaloisSplitTorusQuotientDescent` assumes a smooth affine ground-field
ambient group and a supplied actual torus quotient of its base change. Its
full kernel must be closed, smooth, connected, unipotent and split. The
existing torus-quotient descent constructor supplies the actual ground-field
geometric radical, smooth torus quotient, both recovery isomorphisms and their
commuting equations. The constructor returns that entire data together with
splitness of its own radical. It does not construct the initial
extension-field quotient or its split kernel.

The provenance is composition of the imported effective radical descent,
torus-quotient recognition and comparison, isomorphism transport of actual
split series, and the conditional split-unipotence descent construction.
No new assertion from the literature or additional field restriction is used.
