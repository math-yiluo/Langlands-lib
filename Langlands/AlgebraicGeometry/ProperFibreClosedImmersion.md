# Closed immersion of proper maps detected on residue fibres

This internal derived construction concerns actual residue-field fibres of
scheme morphisms in a fixed arbitrary universe. It is intended to reduce the
remaining relative closed-immersion step for projective evaluation to its
fibre geometry.

`fibreScalarMap` is the scalar map from a prime's residue field to the actual
algebra fibre, the tensor product of that residue field with the algebra.
For a finite algebra, surjectivity of all these maps implies surjectivity of
the original scalar map. The proof takes the cokernel of the original
linear map. Tensoring its quotient map with a residue field is surjective.
Every tensor in the algebra fibre is a scalar times one, and one maps to
zero in the cokernel. Consequently every residue-field tensor of the finite
cokernel vanishes. The finite-module support criterion and empty-support
criterion force the cokernel itself to vanish.

The scheme proof transports fibre closed immersion through Cartesian base
change. For a finite morphism, it reduces along affine target opens and
the canonical affine source isomorphism to a map of prime spectra. Mathlib's
actual arrow isomorphism from a spectrum fibre to the tensor-product fibre
identifies the fibre hypothesis with scalar surjectivity. The algebra
argument then proves that the original map is a closed immersion.

For a proper morphism, closed immersion of all target residue fibres
implies local quasi-finiteness. Properness and local quasi-finiteness give
finiteness by Mathlib's Zariski Main Theorem. The preceding finite criterion
therefore proves the claimed equivalence.

`relativeFibreMap f q s` is an abbreviation for the existing
`baseFibreMap f q s` from `ProperFibreFiniteSpreading`: the actual map from
the fibre of `f ≫ q` to the fibre of `q` at `s`. The fibre-inclusion
identity reuses `baseFibreMap_fiberι`; the residue-field structure-map
identity is proved here. Pullback pasting proves
that it is the actual base change of `f` along that fibre inclusion.

No assertion about generation of any line bundle, direct-image rank,
fibre embedding, or moduli representability is supplied here.
