# Locality of the union of fibre components selected by a section

This internal unit proves that the existing `SectionComponent.componentSet`
commutes with restriction to an open subset of the base, and that its
openness can be checked on an arbitrary open base cover. It reduces the
published finite-presentation openness proposition to affine bases. It
does not prove that proposition.

For a commuting square compatible with the two sections, the previously
published `fiberMap` carries the selected point to the selected point.
If that map of actual residue fibres is an isomorphism, continuity of its
inverse proves the reverse inclusion between the selected connected
components. In a Cartesian square whose base map is an open immersion,
Mathlib's Cartesian comparison of residue fibres identifies this map as
the base change of the residue-field isomorphism. Consequently it is an
isomorphism.

Every point of the source lies in its actual residue fibre. Applying the
fibrewise membership characterization already proved for `componentSet`
and the preceding isomorphism gives
`g ⁻¹' componentSet f e he = componentSet f' e' he'` for an arbitrary
Cartesian square over an open immersion, with compatible sections.
This requires no flatness, finite presentation, geometric reducedness or
separation.

`baseChangeSection` is the actual pullback section for any base map.
The two projection identities follow from the pullback universal property.
The preceding equality specializes to this section over an open base.
For an open cover of the base, its pullback covers the total space.
The original component union is the union of the images of the
restricted component unions. These images are open when the restricted
unions are open, since the cover projections are open immersions.
The converse follows from continuity.

`AffineBaseOpennessStatement` is the affine-base specialization of
`FlatFinitePresentationOpennessStatement`, with all five hypotheses
unchanged and an arbitrary source scheme in universe `u`. The implemented
equivalence applies the open-cover criterion to the canonical affine
cover of the base. Each of flatness, local finite presentation,
quasi-compactness, quasi-separatedness and geometric reducedness is stable
under that base change. The implication in the other direction is direct
specialization.

The provenance is internal: these are consequences of the existing
actual-fibre construction, functoriality, Mathlib's fibre comparison,
and elementary topology. The reduction implements the locality on the
base used at the start of the proof of EGA IV, Troisième partie (1966),
Corollary 15.6.5, printed pp.238–239 (retained PDF pages237–238),
registered source `ega-iv3-grothendieck-dieudonne-1966`, SHA-256
`f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`.
It supplies no Noetherian approximation, constructibility, DVR
connectedness or geometric connectedness theorem. In particular, it
asserts no component-union equality for a general base change.
