# Integral block rotation for lower quotient representatives

This internal derived module places the exact
`TwoBlockLowerUnipotentQuotient.blockRotation h F.Carrier` in the canonical
compact open subgroup `TwoBlockDeformation.integralOpen F t`.
`blockRotation_mem_integralOpen` uses the published coordinate criterion:
the entries of the matrix and its inverse must all belong to the canonical
integer subring. The existing entry formulas give only zero or one, which
both belong to that subring. Subgroup closure then gives
`blockRotation_inv_mem_integralOpen`.

`integralBlockRotation` is the actual rotation bundled as an element of this
integral subgroup; its underlying general linear element is unchanged.
`blockRotation_inv_mul_mem_integralOpen` shows that moving the inverse
rotation into a right integral factor preserves membership.
`blockRotation_inv_mul_image_integralOpen` strengthens this to equality of
the translated set and the entire integral subgroup: the reverse inclusion
uses multiplication by the rotation as a preimage.

These results let compact integral section bounds apply after commuting a
diagonal matrix with the inverse block rotation. The module introduces no
measure or convergence assertion. Its provenance is internal, using only the
published zero-one entry formulas, the coordinate description of the
canonical integral subgroup and subgroup closure.
