# Scheme realization of root-orbit field coordinates

Under the hypotheses of `rootFieldCoordinatesOfOrbit`, let `U → G` be any
affine representative of the actual relative root subgroup. Choose a finite
base-field basis of the actual `rootOrbitField`. This module constructs an
isomorphism of group schemes from `U` to the polynomial vector group in that
basis. In addition to the hypotheses defining the rational field coordinates,
the representative is affine, as required for the actual Lie-module comparison.

`rootFieldVectorIsoOfOrbit` applies the all-test construction in
`RelativeRoot.rootFieldVectorIso` to the existing
`rootOrbitFieldWeightSpaceLinearEquiv`. Thus the linear comparison is constructed
from the actual Galois root orbit; no extra field-to-weight-space equivalence is
assumed.

`sectionCoordinates_rootFieldVectorIsoOfOrbit` proves that its rational section
coordinates are the chosen basis coordinates of the inverse of the existing
`rootFieldCoordinatesOfOrbit.equiv`. The proof applies the generic
root-point Lie-coordinate formula and unfolds that existing rational
equivalence. The centralizer and selected-root hypotheses occur exactly in
that rational comparison; the scheme isomorphism itself only needs the
root-orbit linear comparison.

This derived construction supports the additive root models of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Appendix C.5,
especially Proposition C.5.1 and the use of additive models in C.5.3
(printed pp.703–705 / PDF pp.734–736). The construction is an actual scheme
isomorphism on all tests, including nonreduced schemes. It does not yet prove
that a separately supplied apartment filtration is the root-field valuation
filtration, nor does it prove the unitary cases or the complete C.5.3 target.
