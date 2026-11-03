# Shrinking sections that generate along a proper fibre

This internal geometric module works with the actual scheme-theoretic fibres
and a fixed line bundle in every universe. It proves that a finite family of
sections of one positive tensor power, with affine generation opens covering
the specified fibre, makes the original bundle ample above an affine base
neighbourhood. The sections need only generate along that fibre initially.

The canonical `fibreRestrictionMap` compares the fibre of a base-open
restriction with the original fibre. It commutes with the two inclusions
into the original total scheme. Its affine-morphism instance comes from
Mathlib's fibre pullback square: it is a base change of the affine map
between the two residue-field spectra.

`exists_ample_neighbourhood_of_restrict` converts an ampleness neighbourhood
inside a base open into one in the original base. It takes the image open,
identifies the two iterated source restrictions by their canonical scheme
isomorphism, pulls ampleness back along that isomorphism, and transports the
line bundle using actual pullback composition and congruence isomorphisms.

For `exists_ample_neighbourhood_of_fibre_sections`, properness first shrinks
the base until its inverse image lies in the union of the section generation
opens. Pulling back the sections now gives a generating system on the whole
restricted source. Its fibre generation opens are affine by the affine fibre
comparison above. `FibrePowerSectionSystem.exists_ample_neighbourhood` applies,
and the base-open conversion returns the claimed original restriction.

The provenance is internal, using the published proper shrinking lemma,
actual pullback power sections, fibre pullback geometry, and the previously
proved geometric ampleness adapter. No lifting from fibre sections is claimed:
the finite family here already consists of sections on the total scheme.
