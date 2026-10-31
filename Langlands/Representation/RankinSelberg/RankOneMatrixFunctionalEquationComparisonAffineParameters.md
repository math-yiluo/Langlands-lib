# Actual free-coordinate parametrizations of affine slices

Author: Worker 623.

This internal measure helper identifies the already defined affine slice
measures with actual product measures on their free coordinates. It keeps
the supplied scalar additive Haar measure exactly, with no rescaling.

`finitePiCurry_preserving` groups a finite dependent family of coordinates
into rows. The product of arbitrary sigma-finite coordinate measures is
carried to the nested row product by the actual currying equivalence. No
Haar assumption is used for this general regrouping theorem. The proof uses
uniqueness of product measures on rectangles of measurable rectangles.

`coordinateSliceParam S c` fills the selected row coordinates from their
free scalar values and fixes the others at the entries of `c`.
`coordinateSliceParam_preserving` proves that the product of the supplied
scalar Haar measure over these free coordinates pushes forward to the
published `coordinateSliceMeasure ν S c`. Its proof evaluates measurable
rectangles: if a fixed entry lies outside its prescribed side, both masses
vanish; otherwise exactly the selected-coordinate factors remain.

`RectangularFreeEntry S` indexes free entries by row and selected column.
`rectangularSliceParam S c` fills a matrix from scalar values on these
positions. `rectangularSliceParam_preserving` proves that their product
measure pushes forward to `rectangularCoordinateSliceMeasure ν S c`, whose
nested product measure was used in the actual affine Fourier identity.
The proof combines finite currying with the row parametrization theorem.
All finite dimensions and selected subsets, including empty ones, are
covered. The scalar setting is a field with a topology and measurable space
and a supplied sigma-finite additive Haar measure; no Fourier self-duality
or topological separation hypothesis is used.

The provenance is internal derivation from the published slice measures
and Mathlib product measure uniqueness, Dirac measure and measure-preserving
composition theorems. This module asserts no Fourier or Whittaker identity
and no gamma functional equation.
