# Spherical integration in two-block parabolic coordinates

The preimage of the standard compact subgroup in the existing coordinates
`parabolicPoint h (L, x)` is the product of the integral general linear groups
of both diagonal blocks and the lattice of integral rectangular matrices.
The proof reads the blocks of the ambient matrix and its inverse. It recovers
integrality of `x` by multiplying the integral upper right block by the integral
inverse of the first diagonal block.

The spherical Haar measure and the general linear Haar measure used by the
two-block integration formula agree because their defining positive compact sets
agree. The product formula for measures then gives mass one to the preimage of
the spherical subgroup when the radical Haar gives the integral lattice mass
one. For a right spherical-invariant integrable function, the compact average
in `integral_parabolic` is the constant integrand integrated over a set of mass
one. The integrability formula on the product and the probability measure on
the standard compact subgroup give integrability of the parabolic-coordinate
function.

This specializes the Library's two-block parabolic integration formula to the
spherical measures needed for constant terms. Arthur–Clozel (1989), Chapter 1,
Theorem 4.5 uses the spherical constant term in the reduction to a standard
Levi. The radical normalization here follows from the Library's explicit
measure in `Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar`.
