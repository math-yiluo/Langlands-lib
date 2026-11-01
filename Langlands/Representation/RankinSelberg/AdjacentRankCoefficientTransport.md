# Original-carrier transport for the adjacent-rank lower induction

This internal construction addresses the carrier transport in the JPSS
Section 6.1 adjacent-rank model. The specified Whittaker functional on
the original smooth representation determines its actual coefficient
image, whose carrier lives in universe `uF`, independently of `uV`.
The canonical map onto this image is surjective even when the
functional's coefficient map has a kernel.

The two ordered inducing factors have ranks `(r+1,1)`. The first factor
map is the published `Whittaker.modelMap`. The second is the explicit
linear representation equivalence between the lifted scalar carriers
`ULift.{uV} ℂ` and `ULift.{uF} ℂ`, given by lowering and lifting.
The rank-one character action is identical under this equivalence.
Their external tensor map is surjective by
`FiniteTensor.externalMapSurjectivity`.

`adjacentCoefficientInducedMap` is the published actual normalized
opposite-parabolic induction map of this tensor map. The imported
opposite-induction surjectivity helper proves it is surjective.
Smoothness of the original representation implies smoothness of its
coefficient image; smoothness of the rank-one character is already
published. No topology on either carrier or irreducibility assumption
is used, and `r=0` is included.

`adjacentCoefficientInducedImage_transport` takes a specified nonzero
model-side Whittaker functional and an equality of its entire coefficient
range with any supplied set `S` of functions on the ambient group.
It constructs the pullback functional on the exact original-carrier
induction. The companion `Whittaker.SurjectiveCoefficientTransport`
lemmas prove that this pullback is nonzero and has precisely the same
coefficient range, so it also realizes `S`. Each coefficient is a whole
function on all of `GL_(r+2)`.

The construction is derived transport infrastructure. It does not
establish the existence of the model-side functional, the analytic
image equality, convergence, or section spanning. Its inputs and
proofs use only the cited internal definitions and published algebraic,
smoothness, and induction results. These steps supply the
original-carrier extension of a separate model-side analytic proof.
