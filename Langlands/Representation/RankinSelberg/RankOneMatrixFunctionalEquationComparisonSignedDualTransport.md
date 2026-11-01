# The actual leading-sign and Weyl transport of the dual Fourier integral

This internal derived module proves the group substitution needed to apply the
same-character signed dual pairing to the literal inverse-transpose matrix
integral. It retains the canonical p-adic topology, arbitrary supplied additive
character, supplied additive Haar, and the complete full-matrix Fourier partner.
No self-duality assumption is needed for these covariance identities.

Integral conjugation preserves the principal congruence subgroup because it is
the field-group image of the integral reduction kernel. The leading-coordinate
sign and its inverse have entries in every subring, so the integral-entry
characterization supplies an invertible integral lift. Conjugating
inverse transpose of a principal element by this sign therefore remains in the
same principal subgroup. The signed dual of a principal-fixed function is thus
fixed by precisely that same level.

The box test is invariant under negating its first column. Every changed entry
lies in a lattice centred at zero, while the remaining columns are unchanged.
Full-matrix Fourier covariance transfers this symmetry to every actual Fourier
partner, since inverse transpose fixes the leading sign and its determinant
norm is one. The signed long Weyl determinant also has norm one.

`rankOneSignedDualHomeomorph` is the actual map
`h ↦ signedWeyl * h * leadingSign`. Left and right invariance of the existing
general linear Haar measure prove exact measure preservation. The signed dual
coefficient at `h` is the raw inverse-transpose function evaluated at this map.
The first-column Fourier symmetry and the two determinant norms identify the
complete weighted signed Fourier integrand with the raw matrix integrand
composed with this homeomorphism. Consequently both genuine integrability and
the totalized integral transport exactly, with no scalar or character factor.

The provenance is the existing reduction-kernel definitions, signed Weyl
identities, full Fourier covariance and general linear Haar unimodularity. This
module proves transport, without deriving raw convergence or the final gamma
functional equation.
