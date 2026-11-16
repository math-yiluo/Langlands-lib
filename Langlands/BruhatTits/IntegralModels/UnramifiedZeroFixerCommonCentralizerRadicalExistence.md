# Unconditional common centralizer radical for maximal-unramified models

`UnramifiedZeroFixerCommonCentralizerRadicalExistenceStatement` asserts,
at arbitrary universe `u`, that one subgroup `H` is chosen before every
nonempty apartment subset contained in a single facet, every characterized
smooth integral model, and every represented unipotent radical. It has the
two bounds required by the original upstairs target: it lies in the image
of the actual generic centralizer inclusion and in the intersection of
`E.zeroPoints` with the whole-apartment fixer. For each supplied model and
radical, the actual upstairs radical-preimage image intersects the generic
centralizer-point image in exactly `H`.

The statement uses the original reduction and generic integral-point maps.
It assumes neither boundedness of facets nor global existence of a
characterized model. This is a supporting centralizer-intersection result;
the full upstairs target also requires generation by `H` and the positive
root fixers.

The proof applies the published conditional
`unramifiedZeroFixerCommonCentralizerRadical` to
`torusCentralizerUnipotentRadical`. The accompanying
`Langlands.GroupScheme.Absolute.TorusCentralizerUnipotentRadicalProof`
proves precisely the existing all-test radical-intersection proposition,
without additional structural hypotheses. Its paired Markdown explains
the Borel-containment and Chevalley-envelope argument for one inclusion,
and the smooth connected normal-unipotent intersection argument for the
other. The published common-subgroup construction then supplies the same
uniform witness and both bounds. No geometric premise remains in this
statement.

The provenance is internal composition of the named Library construction
and the accompanying exact prerequisite proof. The source-audited
upstairs target and all its imported statement pairs are unchanged.
