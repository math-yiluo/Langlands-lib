# Central multiplicative quotients and exact Borel descent

Author of the focused proof contribution: Worker 1467.

This module imports the canonical proof from `BorelNormalizerSmoothCentralGm`.
The independently reviewed contribution proved the same proposition under the
same fully qualified theorem name. Integration retains the existing declaration
and exposes it through this focused import, preserving all hypotheses and
conclusions.

`Langlands.GroupScheme.centralMultiplicativeQuotientBorel.{u}` proves exactly
the published `CentralMultiplicativeQuotientBorelStatement.{u}`. The universe
is arbitrary. The hypotheses are the original ones: an algebraically closed
field, a smooth connected affine group scheme `G`, a Borel inclusion
`i : B → G`, and a central closed copy `z : Gm → G` with a specified
factorization `zB : Gm → B`, `zB ≫ i = z`.

The proof constructs a smooth connected affine group scheme `Q` and a
smooth homomorphism `q : G → Q` satisfying
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q`, with
`Lie.dimension Q < Lie.dimension G`. It also constructs an actual Borel
`iQ : BQ → Q` and a smooth homomorphism `qB : B → BQ`, with
`i ≫ q = qB ≫ iQ`, the fppf quotient predicate for `range zB`, and the
exact equality
`(SubgroupFunctor.range iQ).comap q = SubgroupFunctor.range i`.
The equality applies on every relative scheme test.

The canonical construction uses the published
`SmoothNormalQuotient.ofClosedNormal` for a smooth closed normal subgroup
of a smooth affine group over a field. Its chosen quotient is smooth,
separated, locally of finite type and quasi-compact, and its projection is
smooth, surjective and quasi-compact with the specified all-test kernel.
The published theorem `affineGroupSchemeQuotient` applies to this actual
homomorphism: smoothness of the source gives local finite type, and the
fppf predicate gives flatness of the projection. This proves affineness of
the same quotient, without a quotient-existence premise. The existing
`SmoothNormalQuotient.isAffineHom` packages this affineness argument.

For the main theorem, `isCentral_iff_range_le_center` converts the centre
inclusion to `IsCentral z`, and `IsCentral.range_isNormal` proves normality
of its range. The Borel is smooth by definition and affine because its
closed inclusion lands in affine `G`. Closedness of `zB` follows from
closedness of its composite with `i`. Since `i` is monic, the published
`SubgroupFunctor.comap_range_of_factor` identifies `range zB` with the
inverse image of `range z`; normality therefore pulls back to `B`.
The existing `exists_borel_quotients_of_smooth_central_gm` applies this
construction twice, using `smooth_gm`, to obtain the affine fppf quotients
of `G` and `B`.

The published `exists_borel_of_fppf_gm_quotients` then supplies `iQ`,
its full Borel property, the commuting square, smoothness of both
projections, and the exact inverse-image equality. Its construction uses
the compatibility of the actual kernels and the cartesian quotient
square, so it retains arbitrary scheme tests. Finally,
`RelativeRoot.IsFppfQuotient.gm_induction_properties` proves smoothness
and connectedness of `Q` and the strict decrease in the finite rank of
the actual dual-number Lie kernel. The proof assembles all these witnesses
in the exact order of the published target.

This is an internal composition of the named published proof theorems.
The mathematical provenance and original Milne locators are recorded in
the unchanged target Markdown. The implemented proof obtains the Lie
dimension decrease from the existing dual-number Lie theorem rather than
from a separate geometric dimension formula. It takes no
`NormalSubgroupQuotientStatement`, `BorelNormalizerStatement`,
`ParabolicSelfNormalizerStatement` or other structural proposition as an
additional premise. The fppf quotient predicates concern flat surjective
scheme maps with exact represented kernels; the proof does not require
surjectivity on the points of each individual test scheme.
