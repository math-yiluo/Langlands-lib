# Projective coordinate changes of tensor frames

`LocalFrame.projectiveChange` is the actual morphism of the relative projective
scheme over a common original base open, induced by the two frames' dual
coordinate change. Its matrix coefficients are transported by `coordinatesOnOpen`
to global functions on the open subscheme. The identity, composition, and
restriction laws follow from the corresponding frame-coordinate laws and
the naturality of `globalLinearAction`.

For two genuine frames on the same original open and two trivializations of
the same restricted line module, `tensor_dual_change` identifies the tensor
dual-frame coordinate equivalence with the original equivalence followed
by multiplication by the restricted reverse comparing unit.
`tensor_projectiveChange` proves equality of the resulting actual projective
scheme morphisms. The proof transports the scalar unit through the section-ring
map, applies the composition law for projective actions, and uses the already
published triviality of scalar-unit projective actions.

The auxiliary `ProjectiveSpace.coordinateBaseChange_smulOfUnit` proves that base
change of a scalar coordinate equivalence is the equivalence of multiplication
by the image unit. Its proof compares the standard-basis matrix coefficients.

This is derived from the existing tensor-frame coordinate formulas and the
projective action laws. It does not yet compare line trivializations on different
original opens or construct global tensor-line projective invariance. The host
ordinary moduli existence theorem remains a separate obligation.
