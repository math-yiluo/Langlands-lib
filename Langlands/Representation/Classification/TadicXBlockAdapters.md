# Bounded conversion of Tadic X-blocks to actual building blocks

Author: Worker 1745.

This internal unit compares the existing predicates `IsTadicXBlock` and
`IsTadicBuildingBlock` using actual smooth equivariant isomorphisms. The
field and representation universes `uF`, `uV` remain independent and all
representation carriers lie in `Type (max uF uV)`. It derives no new
assertion directly from original literature.

`TadicSocleSpehComparison F T k` packages the exact supplied comparison
needed by this adapter. For any unitary cuspidal datum `ρ`, positive
integers `n,d`, and any actual Zelevinsky socle `σ` of
`tadicMultisegment ρ n d hd` on a rank `N ≤ k`, it requires a Speh datum
`D`, an actual representation `S` of rank `D.degree`, a displayed equality
`h : D.degree = N`, a proof of `D.IsSpeh S`, and an isomorphism
`(h ▸ S) ≅ σ`. The predicate asserts no such witness exists without the
hypothesis. It records only existence of an appropriate Speh realization;
it does not identify the precise transposed rectangular parameters. The
stronger rectangular-parameter comparison remains a separate obligation
in the exhaustion induction. `TadicSocleSpehComparison.mono` restricts a
supplied comparison to a smaller rank bound by transitivity of `≤`.

`isTadicBuildingBlock_of_isTadicXBlock` assumes this comparison at the fixed
bound `k` and converts every member of `X_k` to an actual building block.
For the direct-socle branch it uses the supplied Speh realization as the
first alternative of `IsTadicBuildingBlock`, retaining its rank equality
and actual isomorphism. For the complementary branch it applies the
comparison only to the underlying socle `σ` of rank `M ≤ k`, keeps its
strict interval `0 < α < 1/2`, and eliminates the displayed equality
`2 * M = N`. The previously constructed
`SpehDatum.complementaryRankIso` then identifies the entire doubled-rank
induction with the complementary product of `σ`; composing with the
X-block's supplied isomorphism gives the required building-block witness.
The same supplied Speh representation `S` appears in both complementary
factors and the exponents remain `α,-α`.

The bound concerns the rank of the underlying socle, as in `X_k`; the
final complementary rank `2 * M` need not be at most `k`. No additional
positive-rank assumption is needed: positivity of `n,d` belongs to the
corrected `IsTadicXBlock` definition. This conditional adapter proves
neither `TadicSocleSpehComparison` nor unitarizability nor the final
unconditional `TadicUnitaryDualExhaustion` assertion.
