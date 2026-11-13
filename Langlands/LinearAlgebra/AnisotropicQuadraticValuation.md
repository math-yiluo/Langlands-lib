# Quadratic valuation lattices

This internal auxiliary development constructs the valuation-ring submodules
`Langlands.AnisotropicQuadratic.valueLattice Q hQ r hr` cut out by
`‖Q x‖ ≤ r`, for a nonnegative real number `r`. The ground field is an
ultrametric normed field with Henselian norm valuation ring, the vector space
may have any dimension, and `Q` is anisotropic. There is no restriction on
field or residue characteristic and no nonsingularity assumption. Scalars
act by restriction along the actual valuation-ring inclusion into the field.
The membership lemma identifies the constructed carrier exactly.

The construction is derived from Petersson, *Anisotropic quadratic forms over
local fields* (2013), §2.4, formulas (8)–(9), p. 3. Its generic normed-field
packaging and the sublevel module at an arbitrary nonnegative real threshold
are internal interfaces for the local dimension-bound proof. They make no
claim about finite generation, spanning or quotient dimensions.

The implemented proof first establishes `polar_norm_sq_le`. Writing the
binary restriction as `a s² + b s + c`, a violation of the polar bound puts
`d = a c / b²` in the maximal ideal. The monic polynomial `T² + T + d` has
the simple residue root zero, so the Henselian local ring supplies a root
`z`. Rescaling by `b/a` gives a zero of the binary quadratic restriction.
Anisotropy forces the two vectors to be dependent. Their polar and quadratic
values then satisfy the desired bound because `‖2‖ ≤ 1`, contradicting the
assumed violation. No division by two is used.

The square bound implies `polar_norm_le_max` by nonnegativity. Applying the
field's ultrametric inequality to the quadratic addition identity gives
`norm_map_add_le_max`. This proves closure of each sublevel set under
addition. Quadratic homogeneity and the bound on valuation-ring scalars
prove closure under scalar multiplication; nonnegativity of the threshold
gives the zero vector.

The two residue quadratic forms, their dimension comparison and the final
local dimension bound are separate remaining constructions.
