# Coefficient tensor coordinates for a finite affine cover

This internal derived module converts actual affine scheme overlaps and finite
covers into ring coordinates for coefficient descent.

For affine schemes over an affine base, `overlapTensorEquiv` identifies the tensor
product of the two global-section rings over the base ring with global sections
on the actual fibre product. It compares the canonical tensor pushout with the
affine pullback's global-section pushout. The pure-tensor lemmas identify the two
factors with the two pullback projections and their product.

`coverRingMap` is the base map to the product of a finite affine family's chart
rings. `coverRingMap_faithfullyFlat` proves faithful flatness when the component
maps are flat and their coproduct map is surjective. The finite coproduct is
identified with the spectrum of the product of the chart rings, and the ring
map's spectrum is this cover map after the canonical affine isomorphisms.

`coefficientTensorEquiv` combines finite-product tensor distribution with the
individual overlap equivalences. Its codomain has one global coefficient family
on every actual pairwise overlap, indexed by the target chart's coordinates.
The pure-tensor formula records the projection orientation.

The universe is arbitrary and common to schemes and indices; component coordinate
sets may be empty and have varying finite cardinalities. No transition maps,
coaction laws, or final Weil presentation are asserted by this module.
