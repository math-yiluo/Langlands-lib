# Compact multipliers and induced block operators

`InductionStages.RealInducedCompactMultiplierStatement` concerns the
Library's induced operator `ind` for an exactly compact-equivariant
linear map between two standard modules of the same block rank.
Suppose two standard vectors restrict to \(F(k)=\phi(k)f(k)\) on
the full compact group and \(\phi\) is invariant under the embedded
middle compact group on the left. The two induced images then have
the same multiplication relation on the full compact group.

At a compact element \(k\), the normalized middle slice of \(F\)
restricts to \(\phi(k)\) times the middle slice of \(f\). The slice
factor is one at middle compact elements and the multiplier is
constant on their left orbit through \(k\). The middle restriction
determines the slice by uniqueness of principal-series extension.
The defining formula for the induced operator evaluates the middle
operator on the slice at the identity. Its linearity gives the result.

The provenance is internal to the Library's normalized compact slices
and induction in stages. This commutation allows one polynomial weight
to act on both entries of an induced compact pairing.
