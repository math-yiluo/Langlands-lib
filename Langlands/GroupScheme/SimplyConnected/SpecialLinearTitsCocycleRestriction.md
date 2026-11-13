# Finite-stage restrictions of the original Tits roots

Derived internal infrastructure for `SpecialLinearTitsCocycleStatement`.
The character tower map commutes with precomposition along morphisms defined
over the original base and sends a base-changed original character to its
direct base change. The first proof uses naturality of the pullback-composition
comparison. The second evaluates characters on every relative test, uses
compatibility of the successive pullback point equivalences, and removes the
identity map of the underlying test scheme.

These are consequences of the existing character and base-change definitions,
with no additional literature assertion.

`SpecialLinearTitsCocycle.stageTorusMap` maps the maximal split torus of the
original Tits data into a finite-stage torus by composing `d.torusMap` with the
inverse of the supplied identification of the original tori. If this
identification respects the inclusions into the ambient group, then
`stageTorusMap_square` proves that the composite with the stage inclusion is
the original split inclusion.

`baseChange_rootRestriction_stage` assumes a stage root-datum equivalence
whose weight map is the actual `StarActionFiniteStage.stageCharacter`, as
returned by `exists_stage_torus`. For every root index `a` of the stage datum,
it proves that base change to `L` of
`d.rootRestriction (e.indexEquiv a)` equals the stage root character restricted
along the base change of `stageTorusMap`. The conclusion concerns the original
`TitsIndexData`, rather than a replacement index.

The proof applies the tower map to both characters. A ground-field character
maps to its direct base change; the definition of the original root restriction
then identifies it with the pulled-back absolute root. Compatibility of the
root-datum equivalence with roots, and its prescribed weight map, turn this into
the tower image of the restricted stage root. Finally the tower isomorphism
cancels, and injectivity of the canonical character base-change equivalence for
the split torus recovers equality over `L`.

The field `k`, extension `L`, and universe `u` are arbitrary. The root comparison
requires an `L`-algebra structure on `SeparableClosure k` and the specified
equality of the spectrum structure maps; finite-dimensionality and the Galois
property are unnecessary. The inclusions and root data are actual Library
objects. This module does not construct the special-linear local isomorphism
or prove the full Tits cocycle statement.

The stage-character interface is Worker 243's extension of the finite-stage
construction of Workers 61 and 5375. Its three dependency pairs are reused
unchanged. The additional tower coherence and root-restriction comparison here
are direct consequences of those definitions and the original Tits index.
