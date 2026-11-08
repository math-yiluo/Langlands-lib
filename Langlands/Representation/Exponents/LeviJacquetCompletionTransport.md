# Transport to the normalized actual Levi Jacquet completion

This derived supporting unit makes the group and quotient transports in the
completion argument of Renard, *Représentations des groupes réductifs p-adiques*
(2026), VI.9.7 explicit. Source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
printed pp.205–206 / PDF pp.211–212. The normalization convention is VI.1.2,
printed p.135 / PDF p.141. These transports are internal constructions, not
separately numbered assertions of the source.

The field and representation carrier universes are arbitrary. The field is
Hausdorff and topological. The ambient group scheme has affine structure
morphism; its rational points have the canonical point topology and are
locally compact and nonarchimedean. The data consist of an actual parabolic,
its rational Levi, its geometric unipotent radical, and their multiplication
isomorphism. The representation is any smooth complex representation of
the ambient rational points. No admissibility or finiteness assumption is
used.

`leviJacquetCompletionTransportEquiv` starts from the compatible-family
completion of `Jacquet.action` on the actual radical coinvariants, with its
action by the literal Levi point image in the ambient group. It composes
three explicit equivalences:

1. The inverse of `Jacquet.Localization.trivialEquiv`, applied componentwise
   by `CompactCompletion.equiv`, replaces the concrete coinvariants by the
   localization at the trivial character.
2. `CompactCompletion.pullbackEquiv` reindexes compact open subgroups through
   the actual topological group isomorphism `leviPointsEquiv`. Its result is
   the completion of `leviUnnormalizedJacquetFunctor` on actual Levi points.
3. The inverse of `leviJacquetCompletionNormalizationEquiv` supplies the
   normalized functor `leviJacquetFunctor`. This comparison preserves every
   component because the intrinsic Haar inverse-half character is trivial
   on compact subgroups.

The component formula is definitional: at a compact open subgroup `J` of
the actual Levi points, it applies the inverse trivial-character quotient
equivalence to the original component indexed by the image of `J`, realized
as `compactIndexComap (leviPointsEquiv ...).symm J`.

`leviJacquetCompletionTransport_trivialEquiv_symm_mk` checks that the inverse
quotient equivalence sends `Jacquet.mk v` to `Jacquet.Localization.mk v`.
`leviJacquetCompletionTransportEquiv_natural` assumes two source completion
families are related componentwise by the actual untwisted Jacquet map induced
by an ambient morphism. It proves that their transported components are related
by `SmoothRep.hom ((leviJacquetFunctor ...).map f)`. The proof chooses a
representative of each coinvariant component, applies the two quotient component
formulas, and uses the definitional action of the published functor on classes.
Both representations in this lemma have the same arbitrary carrier universe,
as in the parent naturality clause.

The paired helper `Smooth/CompactCompletionEquiv` supplies only the generic
completion of an actual intertwining equivalence; its Markdown explains that
construction. This transport unit supplies neither a contraction basis nor
compression stationarity or the fixed-completion Jacquet comparison. Both
exact represented-parabolic parent propositions remain separate obligations.
