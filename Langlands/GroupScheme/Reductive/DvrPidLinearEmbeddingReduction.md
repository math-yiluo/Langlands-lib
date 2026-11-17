# DVR matrix reduction using the proved PID embedding

Worker 700. This internal reduction uses the actual closed linear embedding of
flat affine finite-type groups over a DVR. All schemes and rings range over an
arbitrary universe `u`.

`ReductiveDvrPidReductionStatement` is the proposition that
`DvrGenericAffinenessStatement` and `ReductiveDvrMatrixMonomorphismStatement`
imply `ReductiveMonomorphismValuativeReduction.DvrCase`. These are the actual
published propositions; their groups, underlying scheme monomorphisms and
closed-immersion conclusions are unchanged.

`DvrPidLinearEmbeddingReduction.flatAffineCase_of_matrixCase` first proves
`DvrAffineClosureReduction.FlatAffineCase` from the matrix case alone. For a
scheme-monic homomorphism `f : M → G` with reductive source and flat affine
finite-type target over a DVR, the proved
`IntegralLinearEmbedding.exists_isClosedSubgroup_of_dvr` supplies an actual
closed representation `ρ : G → GL_N`. The composite `f ≫ ρ`, represented by
`ρ.restrict f`, is scheme-monic. The supplied matrix case makes that composite
a closed immersion. The closed embedding `ρ` is separated, so the existing
closed-immersion cancellation theorem gives closedness of `f`.

`DvrPidLinearEmbeddingReduction.dvrCase_of_matrixCase` combines this result
with the existing affine schematic-closure reduction, whose explicit input is
Raynaud affineness. Its conclusion is the full published DVR case for reductive
sources and separated finitely presented targets, which need not be affine or
flat. `DvrPidLinearEmbeddingReduction.reduction` records these two implications
as a proof of the proposition defined here.

The provenance is internal composition of the PID/DVR embedding construction,
the existing matrix and affine-closure interfaces, and scheme-level composition
and cancellation of closed immersions. The full Dedekind embedding assertion is
not a premise. Raynaud affineness and the matrix case remain explicit premises;
this module does not establish the unconditional arbitrary-base theorem.
