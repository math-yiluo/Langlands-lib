# One-dimensional unipotent groups over perfect fields

`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement.{u}`
is a proposition definition. It asserts that a connected affine group scheme
over a perfect field, smooth of relative dimension one and unipotent in the
existing fixed-vector sense, is a one-dimensional vector group.

The universe and characteristic are arbitrary. Finite perfect fields are
included. Smoothness of relative dimension one implies smoothness and local
finite type; the affine structure morphism supplies quasi-compactness, so this
is an affine finite-type group over the field. The dimension premise is the
existing scheme-morphism property `SmoothOfRelativeDimension 1`, expressing
constant smooth relative dimension one.

The conclusion is the unchanged
`RelativeRoot.IsVectorGroupOfDimension U 1`. It provides multiplicative
equivalences from `U(T)` to the additive group of one global function on every
relative scheme test `T`, with naturality under every test morphism. This
expresses an actual group-scheme isomorphism with the additive group; it is
stronger than an identification of rational-point groups.

## Original source and use

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field* (2017), paragraph 14.58, printed p.298 / one-based PDF p.314, states
that the smooth connected unipotent one-dimensional conditions characterize
the additive group over a perfect field. Its cited classification is
Corollary 14.53, printed p.297 / PDF p.313. The present proposition records
the converse direction for the affine groups used in the represented-series
construction.

The registered source is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was checked and contains no correction to 14.53 or 14.58.

This module supplies the classification target, without a proof. In the
split-series application, constructing a quotient and proving its dimension
and affineness remain separate obligations. A finite-kernel map to the
additive group does not itself supply the natural coordinates asserted here.
