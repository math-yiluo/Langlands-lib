# The proper-family affine-neighbourhood reduction

`properFibreAmpleAffineOpen_of_spreading` proves
`ProperFibreAmpleAffineOpenStatement` under the explicit premise
`ProperFibreAmpleSpreadingStatement`, in the same arbitrary universe.
It is an internal derived reduction between the two Library propositions,
using the generic affine-neighbourhood theorem
`exists_isAffineOpen_of_finite_of_ample`.
`properFibreAmpleAffineOpenReduction` packages this theorem as the named
proposition `ProperFibreAmpleAffineOpenReductionStatement`.

For a proper morphism `f : X ⟶ S`, a line bundle `L` ample on the fibre
at `s`, and a finite set `E` of points above `s`, the spreading premise
supplies an affine open neighbourhood `V` of `s` on whose inverse image
the specified bundle is ample. Let `U` be this inverse image as an open
of `X`. Every point of `E` belongs to `U`, since its image is `s`.
The inverse image of `E` under the inclusion `U.ι` is finite because that
inclusion is injective.

Apply the generic theorem to the restricted bundle on `U` and this
finite set, with the prescribed open equal to the whole of `U`.
The resulting affine open maps to an affine open of `X` under the
open immersion `U.ι`. For every point of `E`, its lift to `U` lies in
the constructed open, giving the required image-membership witness.
The argument includes the empty finite set and does not require
points to be closed or schemes to be reduced.

The proof retains the exact properness, local noetherianity, fibre and
line-bundle hypotheses of the published target. It does not discharge the
spreading premise; the unconditional proper-family theorem still needs
a proof of `ProperFibreAmpleSpreadingStatement`.
