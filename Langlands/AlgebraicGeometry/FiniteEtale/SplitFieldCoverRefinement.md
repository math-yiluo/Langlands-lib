# Pointed Galois refinements of split finite étale field covers

The geometric points of the spectra of a field and an extension field use one
algebraically closed coefficient field and the given scalar tower.
`ringPointOfFixedGeometricLift` carries the chosen lift to the pullback cover,
uses equivariance to exhibit it as a fixed point, and composes the section
through that lift with the projection of the pullback.

In characteristic zero, `splitFieldCoverRefinement` starts with the actual
coordinate map of a chosen geometric lift. Its image is a finite field extension
because the cover is finite. Every embedding of that image gives another
geometric lift, and if the extension field's group fixes the entire fibre, each
of those lifts comes from a point over that field. Surjectivity onto the image
then puts every conjugate in the extension field. The normal closure yields a
finite Galois extension equipped with an embedding into the extension field.
The `GaloisFieldCoverLift` records its map of covers and the equality carrying
the chosen lift to the original one.

These are derived constructions using the finite étale fibre action and
Mathlib's normal closure of fields.
