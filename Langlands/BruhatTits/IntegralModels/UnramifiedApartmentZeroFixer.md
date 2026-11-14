# The zero fixer of the whole unramified apartment

This internal comparison uses supplied maximal-unramified building data `C`
and zero data `E` for the original group over the inertia fixed field of a
nonarchimedean local field, at arbitrary universe `u`. The explicit hypothesis
`hE` says that the original inclusion `E.i` represents the entire centralizer
of `C.i`, on every test scheme. It identifies no replacement point group or
building action.

The theorem `compatibleApartmentZeroFixer_eq_torusIwahori` identifies the
intersection of `E.zeroPoints` with the pointwise fixer of the whole original
apartment image with the image of `E.torusIwahori` under `E.i`.
The equivalence `compatibleApartmentZeroFixerEquiv` retains each element's
ambient rational point.

The helper transports a torus point through the canonical isomorphism between
the two representatives of the centralizer. Apartment injection and the
integer-valued centralizer stabilizer comparison show that fixation of one
apartment point, together with membership in the ambient character kernel,
forces membership in the centralizer character kernel. Transport back and
equivalence of the normalized and fixed-field valuations give the stated
character kernel on `E.T`.

For the forward inclusion, the arbitrary-field whole-apartment fixer theorem
puts the point in the actual centralizer, hence in the original image of
`E.T`. Ambient zero points lie in the character kernel, and the preceding
helper supplies the torus character kernel. The compatible torus intersection
theorem then puts the torus point in its norm-defined Iwahori subgroup. For the
reverse inclusion, the defining torus image lies in zero points, while the
compatible Iwahori fixation theorem fixes every apartment point.

The provenance is internal: the proof composes the generic apartment-fixer
containment, integer centralizer stabilizer, zero-subgroup character containment,
compatible torus intersection, and compatible Iwahori fixation theorems. This
result constructs no integral model and does not complete the host parahoric
model theorem.
