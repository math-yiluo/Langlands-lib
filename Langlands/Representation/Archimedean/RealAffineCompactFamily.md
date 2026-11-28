# Simultaneous exponent shifts and compact transport of real block maps

`shiftedBlocks` moves each complex block exponent by the product of the
parameter and the assigned slope. The parity of a character block and the
weight of an induced block stay fixed. `positionExponent_shiftedBlocks`
computes the exponent shift at every diagonal position. The two positions of
an induced block have the same slope, since their internal weight offsets
stay fixed. `isExponentShift_shiftedBlocks` supplies the corresponding compact
linear equivalences.

`compactEquiv_blockFrobMap` shows that these equivalences transport a block
map between the fixed models to the block map of the same symbol between the
shifted models. The equality follows from the compact Fourier formula, since
all compact values of the input are preserved.

`RealAffineCompactFamilyStatement` gives the real Lie intertwining equation
on fixed compact models at a single parameter. It assumes block Frobenius
data for the same symbol on both pairs of models, and the recurrence for the
shifted exponents. The proof uses `blockFrobMap_rightDerivative` on the
shifted models and conjugates the result by the compact equivalences.
`transportedLie_eq_affine` then expresses the two conjugates using the base
Lie operators and their slope increments.

The simultaneous deformation and transport follow from
`RealCompactExponentFamily` and the compact-value formula in
`RealExponentDeformation`.
