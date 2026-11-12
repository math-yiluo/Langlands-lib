# Ordinary points after composition of bases

Author: Worker 109.

This internal construction derives invariance of ordinary points and their
actual point topology from the concrete base composition in
`BaseCompositionGeometry`. No external literature assertion is claimed as
proved here. The schemes, fields and tests are at arbitrary universe `u`,
with section values in `Type (u+1)`.

For any scheme morphism `g : S ⟶ T`, `fieldPoint g` takes a field-valued
section over `S` to the same field and section with its structure map
composed with `g`. `originalFieldPoint g` recovers the original structure
map and section from a composed field-valued section. These operations are
inverse: the defining equation of the composed section identifies its
prescribed `T`-structure with the composite of its original structure map.

The operations respect the actual common-field relations defining ordinary
points. `fieldPoint_rel` composes the base-map equation with `g` and compares
the restrictions using naturality of `OriginalBaseTransport.totalFiberIso`.
Conversely, `originalFieldPoint_rel` first projects equality of composed
sections to identify the original structure maps after field extension.
The same naturality comparison then identifies the original sections over
that common structure map. This includes the structure-map compatibility,
not just an equality of section coordinates.

`pointsEquiv g F` descends these operations to inverse maps on the quotient
point sets for every presheaf `F`. `pointsEquiv_naturality` proves that the
identification commutes with every original natural transformation and its
base composition. Consequently `surjective_spaceMap` preserves general
point-surjectivity of a morphism of algebraic spaces, with no
representability assumption and no hypothesis on `g`.

`schemeComparison_points` and `schemeIso_points` compare ordinary points of
represented schemes. They agree with the identity on the same underlying
scheme: the ordinary scheme-point comparison evaluates the canonical
residue-field morphism at its closed point. `pointsEquiv_chartPointMap`
then identifies the actual point map of every original scheme chart with
that of its `fromScheme` composition.

`pointsHomeomorphOfAtlas` assumes a supplied etale surjective atlas of `F`.
It transports that atlas by `relative_fromScheme`; the underlying source
scheme is unchanged. Both atlas point maps are quotient maps for the
respective point topologies by `isQuotientMap_chartPointMap`. Their agreement
under `pointsEquiv` proves continuity in both directions. `pointsHomeomorph`
uses an actual atlas of an algebraic space, and its underlying equivalence
is exactly `pointsEquiv` on the original presheaf. Thus composition of
bases leaves the ordinary topological space unchanged for every actual
algebraic space. These are the `pointTopology` topologies of ordinary
quotient points, not the local-field point topologies or adelic topologies.

This module does not yet compare geometric fibre presheaves or prove
connected-fibre transport, structural quasi-separatedness, or an adelic
open-map result. Those remain separate obligations for the unchanged
unconditional target.
