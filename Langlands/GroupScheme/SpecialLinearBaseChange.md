# Base change of the actual special linear group

This internal construction identifies the pullback of the existing special
linear group scheme with the existing special linear model over the new base.
The index type is any finite type in `Type`, as in the existing special linear
model; the base rings are arbitrary commutative rings in universe `u`, and the base morphism is any morphism of
their spectra.

For every relative test scheme, pullback adjunction identifies points of the
base-changed group with points of the original group on the test scheme viewed
over the original base. The existing matrix point equivalence identifies these
with determinant-one matrices over the test scheme's global sections. Viewing
the test scheme over the original base leaves those sections unchanged, so the
new-base matrix equivalence gives a natural multiplicative equivalence with
points of the new-base model. `baseChangeModelIso` is the isomorphism obtained
from this equivalence by the existing group-valued Yoneda construction.
`pointsEquiv_baseChangeModelIso_hom` states its full matrix compatibility on
every test scheme.

The result is derived from pullback adjunction, the published all-test matrix
description of the actual special linear scheme, and Yoneda. It requires no
classification or field hypothesis.
