# Depth models on actual root-orbit field coordinates

Fix the hypotheses of `rootFieldVectorIsoOfOrbit`: a connected reductive group
over `k`, a split torus contained in a maximal torus split by a finite Galois
extension `L/k`, a nonzero relative root with no higher positive multiples, an
absolute root whose Galois orbit equals its restriction fibre, and an affine
representative of that actual relative root subgroup. Choose a base-field
basis of the actual root-orbit fixed field. The base field also has a
surjective integer-valued multiplicative valuation and a Henselian valuation
ring.

`rootFieldDepthModelOfOrbit` transports the actual separable valuation-depth
lattice model through the actual root-field scheme isomorphism. The integral
group is a polynomial vector group over the base valuation ring. The models
are smooth with geometrically connected fibres. Their actual depth-inclusion
maps extend the identity on the original root representative. Every compatible
extension of that identity has a smooth, connected and unipotent
scheme-theoretic special-fibre kernel, by the transported separable matrix
kernel theorem.

When the maximal torus represents the centralizer and the selected absolute
root belongs to the restriction fibre, the exact rational-coordinate formula
for `rootFieldVectorIsoOfOrbit` identifies model membership with the normalized
valuation bound in the existing `rootFieldCoordinatesOfOrbit` coordinates.
`rootFieldDepthModelOfOrbit_integralPoints_map` proves equality of the
ambient integral-point image with `additiveRootFiltration` for those published
coordinates. Its proof pulls an ambient root point back through the actual
representing inclusion and applies the membership criterion in both directions.

This is derived infrastructure for the additive cases of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Appendix C.5, Propositions C.5.1
and C.5.3 (printed pp.703–705 / PDF pp.734–736), using the additive models
of Appendix C.2. It applies to the actual root group and actual root field,
including ramified finite separable root fields. It does not identify a
separately supplied apartment filtration with this coordinate filtration,
compare arbitrary supplied integral models with these models, or handle
unitary root groups. The full `UnramifiedRootDepthKernelStatement` remains a
separate obligation.
