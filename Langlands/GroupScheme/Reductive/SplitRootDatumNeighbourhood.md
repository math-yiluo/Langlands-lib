# Open neighbourhoods preserving a full coordinate root datum

This internal construction supports the proof of Conrad, *Reductive group
schemes* (2014), Lemma 5.1.3, pp. 136–137, by spreading the actual full
coordinate root datum near a point. Its proof uses the published actual
transporter and adjoint weight modules; these are not additional assumptions
on reductive groups.

For an integral coordinate automorphism `C`, `coordinateTransporter` is the
actual affine transporter between the torus map twisted by the inverse
exponent automorphism and the original torus map. `realizationLocus` is its
image in the base. The transporter is smooth if the ambient affine group is
smooth, so this image is open. Any realization over a supplied field puts its
image point in this open. Conversely, a field point in the image has a
realization over an extension field: take a point of the transporter fibre
product and its residue field. The construction retains the original
coefficient map through an explicit scalar tower.

`CoordinateRootDatum.rootRange_eq_of_weightRanks` compares two actual
coordinate root data over field-valued points of an arbitrary ring. A
coordinate vector is a root exactly when it is nonzero and its actual
adjoint weight dimension is nonzero. Scalar extension identifies that
dimension with the relative weight rank at the image point. Equality of
these ranks therefore gives equality of the root ranges. This comparison
does not assert that equal root ranges alone determine the coroots.

`LocalSplitCorootTransport.exists_open_isRootDatumOf` intersects the open
weight-rank neighbourhood with the transporter images of the finitely many
reflections in the chosen datum. On each field point of the intersection,
each chosen reflection is realized after a field extension. Its product
with the reflection belonging to any actual datum at that point has finite
order, since both belong to the finite Weyl image over that extension.
The published finite-order reflection comparison then identifies the
coroots, giving an equivalence fixing both entire lattices. This transports
the actual root-datum property to the chosen datum.

`exists_open_coordinateRootDatum` applies this construction to a split
fibrewise maximal torus in a reductive group over an arbitrary affine base.
The initial datum is chosen over the residue field of the specified point,
using the published field root-datum existence theorem. The published
field root-line theorem also shows that its relative root summands have
rank one at that point. The conclusion concerns all supplied field
algebras whose image lies in the resulting open, retaining their original
algebra structures.
