# Actual recognized-pair transport for full quasi-isomorphisms

Author: Worker 208.

This derived internal helper extends `QuasiIsoFiniteEtale` from chosen
saturation extensions to every strong quasi-isomorphism between constructed
saturations. It also proves right cancellation for full quasi-isomorphisms.
It does not establish localized étale stability or pointwise lifting.

Let `K : Type u` be a complete ultrametric normed field, with independent
space and original atlas-index universes `v` and `w`. For presentations
`A, B`, let `g : StrongHom A.saturatedPresentation B.saturatedPresentation`
and `hg : g.IsQuasiIso`.

`IsQuasiIso.isFiniteEtale` restricts `g` to its compatible original bounded
family. The published original-restriction theorem preserves the full
quasi-isomorphism property. Applying
`saturationExtension_isFiniteEtale` to that family and using the exact
recovery of its extension proves `g.IsFiniteEtale`.
`IsQuasiIso.isEtaleAllPieces` applies the existing finite-étale consequence.

`IsQuasiIso.fullRecognitionPairs_represents` uses the same recovery to show
that the actual pullback on each recognized pair `V, W` represents
`W.chart ⁻¹' (g.baseMap '' V.locus)`. The definition
`IsQuasiIso.fullRecognitionPairEquiv` applies `Represents.univEquiv` when
that relative image is the whole spectrum. Its following
`toBoundedAlgHom` theorem preserves exactly the actual pair-system map,
including its bounded algebra structure.

For arbitrary strong maps `f : StrongHom A B` and `g : StrongHom B C`,
`IsQuasiIso.of_saturatedComp_right` assumes that the atlases of `A` and `B`
contain all local domains and that both `g` and their saturated composite
are full quasi-isomorphisms. It proves that `f` is a full
quasi-isomorphism. The ambient homeomorphism is the composite homeomorphism
followed by the inverse homeomorphism of `g`. On each admissible source and
middle chart, choose a target chart for `g`. The saturated-composition law
identifies the composite pullback. The full representation of `g` and its
injective spectrum map allow `Represents.of_comp_of_injective` to cancel
that outer domain. Ambient injectivity of `g` identifies the resulting
inverse-image locus with `f`'s actual chart-image locus.

The implementation uses the Library's original-restriction recovery,
full-domain universal properties, and composition of actual bounded maps.
No external result, supplied inverse morphism, Hausdorff hypothesis or
unproved geometric statement is used.
