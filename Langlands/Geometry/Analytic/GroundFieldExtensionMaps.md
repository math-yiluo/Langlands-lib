# Ground field extension of compatible strong atlas maps

`AffinoidAtlasPresentation.GroundFieldExtension.compatibleMap K L f`
extends a `CompatibleStrongHom` between arbitrary presented atlases over
`K` to one between their quotient presentations over `L`. The fields
are complete ultrametric normed fields with `NormedAlgebra K L`. The
construction allows trivial valuations, arbitrary degree and transcendence
degree, nonreduced and zero chart algebras, and empty spectra and atlases.
`CompatibleStrongHom.ofSaturated` supplies the input compatibility for
every `StrongHom` whose source contains all local affinoid domains.

For an admissible source and target chart pair, `chartMap` takes the
spectrum map of the extended bounded pullback and follows it by the
target chart embedding. To compare two target choices at a point of
the extended source chart, `chartMap_independent` finds an original
common target subchart through the image of the projected point. It
pulls that subchart back to an affinoid domain of the original source
chart. `PresentedAffinoidAlgebra.GroundFieldExtension.domainPreservation`
lifts the point to the extension of this domain. The extended local
compatibility equation gives a point of the common extended target
subchart that represents both images in the quotient. The source
restriction equations then give `pointMap` on the quotient of the
source chart spectra. This map is continuous by the quotient topology
and commutes with the projections to the original spaces.

`admissible_iff` identifies the admissible chart pairs before and after
extension using the chart projection image and preimage formulas.
`strongMap` gives every admissible pair its extended bounded pullback.
Its chart equations follow from `pointMap_chart`, and its restriction
equations follow by applying scalar extension to the original equations.

`strongMap_compatible` compares the extension of an original inverse-image
domain `Q` with the actual inverse-image domain `Q'` formed over `L`.
Both are domains in the extended source chart. The map to the spectrum
of that chart from the spectrum of `Q'` lands in the inverse image of
the original domain locus by naturality of the spectrum projections.
The universal property of the extended `Q` thus gives a bounded map
`Q_L → Q'` over the extended source chart algebra. By uniqueness
for the extended target restriction, composing the extended map from
the common target subchart algebra to `Q_L` with `Q_L → Q'`
gives the pullback map to `Q'`. Composing the extended compatibility
equation with `Q_L → Q'` proves the required equation on `Q'`.

This construction implements Berkovich's ground field extension on the
Library's chosen presentations. The source describes ground field
extension by gluing in §1.4, printed p. 30 (PDF p. 27), and uses
compatible chart maps and their extension to saturated atlases in
Definition 1.2.7 and Proposition 1.2.8, printed p. 18 (PDF p. 15).
The registered source is `berkovich-1993-etale-cohomology`, Vladimir G.
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993).

## Counterexample for weak strong maps

A `StrongHom` can fail to extend with the prescribed extended
pullbacks. Take the trivially normed fields `K = F₂` and `L = F = F₄`.
The source has a sole chart with algebra `F × F`. Its two points map to
`a` and `b` in the target with four points `a`, `b`, `c`, `d`. The
target atlas contains the triple charts `{a,b,c}` and `{a,b,d}` and
the singleton charts. Its selection omits common subcharts of the two
triples that contain the whole source image. The pullback from the first
triple projects onto the two source factors. The pullback from the
second triple composes that projection with Frobenius on the factors.
The twist fixes points over `F₂`. Over `F`, each factor splits as
`F ⊗[F₂] F ≃ F × F`, and the twist interchanges the split points.
The two extended pullbacks then prescribe different images of a source point.

This example concerns the Library's `StrongHom` conventions. The witness
is `Langlands.Analytic.GroundFieldExtensionCounterexample.weakMap`.
Its non-extension assertion is `Langlands.Analytic.GroundFieldExtensionCounterexample.NonExtensionStatement`,
with theorem `Langlands.Analytic.GroundFieldExtensionCounterexample.nonExtension`
in module `Langlands.Geometry.Analytic.GroundFieldExtensionCounterexample.NonExtensionProof`.
The statement and its proof are separate modules,
`GroundFieldExtensionCounterexample.NonExtensionStatement` and
`GroundFieldExtensionCounterexample.NonExtensionProof`.
[Witness construction](GroundFieldExtensionCounterexample/WeakMap.md)
