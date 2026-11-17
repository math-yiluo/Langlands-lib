# Fppf locality and commutativity of relative multiplicative-type groups

Worker 875.

This module proves basic consequences of the published relative predicate
`Langlands.GroupScheme.RelativeMultiplicativeType.IsMultiplicativeType`.
It is an internal derivation from that definition and the existing cover,
base-change and commutativity lemmas. It does not prove
`MultiplicativeTypeFpqcExtensionStatement`.

All schemes and the indexing types of covers are in the arbitrary universe `u`.
There are no affineness, finite-presentation or flatness assumptions on the
group in these results.

`IsMultiplicativeType.of_fppfCover` composes an fppf cover of the base with
chosen diagonalizing fppf covers of its members. The indexing type is the
dependent sum of the two indexing types. The published `baseChangeCompIso`
identifies each direct pullback along a composite covering map with the
successive pullbacks. Diagonalizability transports through that isomorphism.
`isMultiplicativeType_iff_fppfCover` combines this implication with the
published base-change preservation theorem.
`IsMultiplicativeType.of_fppfBaseChange` applies the cover theorem to the
singleton cover associated with a flat, surjective morphism locally of finite
presentation.

`IsDiagonalizable.isCommMonObj` uses the group isomorphism to the actual
commutative diagonalizable model: the induced multiplicative equivalence
on points detects commutativity on every test scheme.
`IsMultiplicativeType.isCommMonObj` then uses the published
`Langlands.GroupScheme.isCommMonObj_of_fppfCover` to descend these equalities.
`isCommMonObj_of_fpqcBaseChange` uses the published
`Langlands.GroupScheme.isCommMonObj_of_baseChange` to obtain commutativity
when multiplicative type is known after a flat, surjective, quasi-compact
base change. This last theorem concludes commutativity only.

`IsMultiplicativeType.commGroupScheme` bundles this proved commutativity on
the original group scheme. Its `commGroupScheme_toGrp` theorem records that
forgetting the extra commutativity structure returns that same group.

The imports provide the relative multiplicative-type definition and its
base-change comparisons, together with the general commutativity descent
lemmas from the existing torus development. No torus or smoothness premise
is used in the results of this module.

This module is the shared home of the existing relative multiplicative-type
commutativity and fppf-cover declarations. The character, geometry and subgroup
modules import these declarations with their original meanings and names.
