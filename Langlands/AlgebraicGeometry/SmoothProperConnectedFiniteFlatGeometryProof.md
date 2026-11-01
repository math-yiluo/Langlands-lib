# Integral geometry and constant positive native rank

`smoothProperConnectedFiniteFlatGeometry` proves the full proposition
`SmoothProperConnectedFiniteFlatGeometryStatement` over an arbitrary field.

The proof installs the given actual geometric morphism properties as local
instances. The existing smooth geometric integrality theorem implies
integrality over `Spec K`. Properness gives compactness, and local finite
type over the field gives local Noetherianity.

The upper dimension bound is the existing smooth dimension theorem. For
the lower bound, compactness and nonemptiness give a closed point. Its
stalk has Krull dimension `g` by the existing closed-point theorem.
Mathlib identifies stalk dimension with coheight in the specialization
order, which is bounded by the space dimension through the order
isomorphism with irreducible closed subsets.

The finite irreducible endomorphism theorem gives surjectivity. Mathlib's
local constancy of the native rank, combined with connectedness, makes
that rank constant. Its native rank/surjectivity comparison gives positive
rank at every target point.

This argument does not use ampleness or a polarization and does not
calculate the constant rank. It proves only the geometric preparation
described by its target.
