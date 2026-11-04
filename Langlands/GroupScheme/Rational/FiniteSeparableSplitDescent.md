# Finite-separable descent of represented split series

This internal construction reduces finite-separable descent of split
unipotence to the existing conditional finite-Galois descent theorem. It
retains the explicit premise
`SplitUnipotentStableVectorSubgroupStatement.{u}`. It does not prove that
premise or the full rational maximal-torus conjugacy statement.

All fields have the same arbitrary universe `u`. There is no restriction on
characteristic, cardinality or perfection. The group is affine throughout.
The final descent theorem additionally assumes that it is smooth, connected
and unipotent in the existing representation-theoretic sense.

`HasSplitSeries.baseChange_fieldTower` starts with a represented normal
additive-group series on the original group after extension from `k` to `L`.
For any compatible field tower `k → L → K`, arbitrary scalar extension of
that actual series gives one on the iterated extension. The inverse of the
existing `baseChangeFieldTowerIso` transports it onto the direct extension
of the original group from `k` to `K`. The same finite length is preserved.
Affineness of the first scalar extension follows by pullback. The companion
`IsSplitUnipotent.baseChange_fieldTower` forgets the chosen length.

`IsSplitUnipotent.exists_finiteGalois_of_finiteSeparable` embeds the supplied
finite separable extension into a separable closure of the ground field and
takes its normal closure there. Existing field-theory instances make that
normal closure finite Galois over `k` and give the compatible algebra tower.
The preceding tower lemma extends the supplied represented series to the
direct scalar extension of the original group to this finite Galois field.
This step needs only affineness of the original group, not smoothness,
connectedness or representation-theoretic unipotence.

`IsSplitUnipotent.of_finiteSeparable_of_stableVector` applies the existing
conditional finite-Galois descent theorem to that normal-closure splitting
field. Its smoothness, connectedness, affineness and unipotence hypotheses
are those on the original ground-field group. The stable-vector theorem
remains an explicit argument. The definition
`finiteSeparableSplitSeriesOfStableVector` chooses a finite length and its
actual `HasSplitSeries` proof on that same original group. Its ground-field
length is not asserted to equal the initial extension-field length.

The provenance is internal composition of arbitrary-field scalar extension
of represented split series, isomorphism transport, the existing direct
versus iterated base-change comparison, the field-theoretic normal closure,
and conditional finite-Galois split-unipotence descent.
