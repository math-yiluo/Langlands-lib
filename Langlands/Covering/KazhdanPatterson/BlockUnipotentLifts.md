# Canonical splittings of standard block unipotent radicals

A standard block unipotent radical consists of block upper triangular
matrices with identity diagonal blocks. The blocks occupy consecutive
coordinates, so the radical is contained in the full upper-unipotent
subgroup of \(\mathrm{GL}_r(F)\).

Suppose the natural number \(e\) is nonzero in \(F\). Take the unique
upper-unipotent \(e\)-th root of an element of the radical. This root is
in the standard parabolic, since every upper triangular invertible matrix
belongs to it. Each diagonal block of the root is upper unipotent and its
\(e\)-th power is the identity. Injectivity of powers on that block makes
the diagonal block itself the identity. Thus the root is in the radical,
and `unipotentSubgroupPowerEquiv` restricts the power bijection to it.

The radical inherits nilpotence from the full upper-unipotent subgroup.
For a surjection onto \(\mathrm{GL}_r(F)\) with central kernel killed by
\(e\), `blockUnipotentSplitting` gives the unique homomorphic lift of the
radical. By uniqueness this lift is the restriction of the full
upper-unipotent lift.

This is an algebraic consequence for standard parabolics of the
upper-unipotent splitting used in Kazhdan–Patterson, *Metaplectic forms*,
§0.1, printed p. 43 (PDF p. 10). Continuity requires topology on the
extension. [DOI 10.1007/BF02698770](https://doi.org/10.1007/BF02698770)
