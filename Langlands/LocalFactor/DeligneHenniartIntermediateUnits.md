# Unit levels at an intermediate field of the common closure

Supporting definitions and lemmas for the dimension-one case of
Deligne–Henniart 1981, Lemma 4.7 (printed pp. 110–111, PDF pp. 22–23). For a
finite intermediate field `E` of the common closure of `F`, the proof needs
the reciprocity image of the upper ramification groups of the Weil group of
`E`. This gives the conductors of characters of `E^×`. This is the
Weil-group form of the upper-numbering theorem (Serre, *Local Fields*,
XV §2, Corollary 3 to Theorem 1) on `E` itself.

The published module `DeligneHenniartUpperUnits` proves that statement for a
geometric standalone candidate (`upperGroup_map_reciprocityUnits`). It also
transports it to the bottom component of a common-closure family. This module
does the same for an arbitrary intermediate field `E`. The geometricity of the
transported component is an explicit hypothesis. The module states it as a
separate proposition, `IntermediateGeometricStatement`.

## Definitions

- `intermediateReciprocityCandidate F eC E` (definition): the standalone Weil
  reciprocity candidate of the p-adic field `E.asPadicField` obtained from the
  component `eC E` of a common-closure family. It precomposes `eC E` with the
  map on topological abelianizations (`abelianizationCongr`) induced by the
  published identification `intermediateWeilEquiv F E` of the standalone local
  Weil group of `E` with the fixing subgroup `W_E = weilSubgroup F E`.
  `reciprocityUnits_intermediateReciprocityCandidate` records, by `rfl`, that
  its reciprocity map is `reciprocityUnits F eC E ∘ intermediateWeilEquiv F E`.
- `IntermediateGeometricStatement` (definition, a proposition): for every
  prime `p`, p-adic field `F`, common-closure family `eC` satisfying
  `NormalizedReciprocity F eC`, and finite intermediate field `E`, the
  candidate `intermediateReciprocityCandidate F eC E` satisfies
  `GeometricWeilReciprocityRelation` for the canonical topological data of
  `E.asPadicField`. It is not proved here.

  The published `CommonClosureGeometricStatement`, clause 2, makes the same
  assertion for `extensionReciprocityCandidate F E' g eC`. That candidate
  identifies the Weil group of a standalone extension `E'` with the fixing
  subgroup of its image field `extensionFiniteIntermediate F E' g`, via
  `extensionImageWeilEquiv`. For `E' = E.asPadicField` and
  `g = intermediateEmbedding F E`, the published `intermediateWeilMap` is that
  map followed by conjugation by `intermediateClosureCorrection F E`, an
  absolute Galois element. The image field is in general a conjugate of `E`.
  Deriving `IntermediateGeometricStatement` from clause 2 therefore needs a
  conjugation argument through the family's conjugation relation. This module
  does not attempt it.
- `intermediateUpperGroup F E s` (definition): the image in `W_E` of the
  upper ramification group `upperGroup (E.asPadicField) s` of the standalone
  Weil group of `E`, under `intermediateWeilEquiv F E`.
  `mem_intermediateUpperGroup`: `g` lies in it exactly when
  `(intermediateWeilEquiv F E).symm g` lies in `upperGroup (E.asPadicField) s`.

## Main theorem

`intermediateUpperGroup_map_reciprocityUnits` has these hypotheses:

- `hreal : AbsoluteReciprocityRealUnitImages`;
- `hcmp : UnitFiltrationComparison`;
- `hinert : AbsoluteUpperInertia` for `E.asPadicField` and its canonical data;
- geometricity of `intermediateReciprocityCandidate F eC E`;
- `s ≥ 0`.

Under these hypotheses, `reciprocityUnits F eC E` maps
`intermediateUpperGroup F E s` onto the principal units of level `⌈s⌉₊` of
`fieldData F E`. Proof: apply the published `upperGroup_map_reciprocityUnits`
to `E.asPadicField` and the intermediate candidate. Rewrite the unit
filtration with `UnitFiltrationComparison`, then compose the two images
(`Subgroup.map_map`). The canonical data of `E.asPadicField` is
`fieldData F E` by definition.

## Scope

The module proves none of the four propositions used as hypotheses, and in
particular not `IntermediateGeometricStatement`. It does not compare
`intermediateUpperGroup` with the upper groups of `F`; that is Herbrand's
theorem for subextensions.
