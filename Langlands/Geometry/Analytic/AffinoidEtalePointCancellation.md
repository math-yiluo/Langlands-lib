# Pointwise étale cancellation for bounded affinoid morphisms

Let `f` and `g` be composable finite-type bounded algebra maps. Suppose
`g.comp f` is étale at a spectrum point and `f` is unramified at its
image under `g`. Then `g` is étale at the original point.

The proof uses the prime ideals that are the kernels of the spectrum
points. It rewrites pointwise unramifiedness as formal unramifiedness
over the localized rings. Unramifiedness of `g` follows by restriction
of scalars from the composite. Flatness of the composite gives
flatness over the local ring of the first algebra. The intermediate
local ring is essentially of finite type and formally unramified over
that ring, so Mathlib's flatness theorem for this algebra tower gives
flatness over the intermediate local ring.

This internal calculation supplies the pointwise input to the
Library's analytic étale cancellation reduction. The published
finite-pieces upgrade gives its second input. Given finite right
cancellation over a common open base, the resulting cancellation
for all pieces applies to the canonical saturations of strong
morphisms, and the fraction-transport theorem gives cancellation
for the localized étale predicate.
