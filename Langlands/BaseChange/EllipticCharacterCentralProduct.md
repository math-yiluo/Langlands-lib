# Central translation and the elliptic character product

Lean module: `Langlands.BaseChange.EllipticCharacterCentralProduct`.

## Regular ellipticity and central translation

`isRegularElliptic_center_mul`: over a field of characteristic zero, multiplying a regular
elliptic element of `GL_n(F)` by a central element gives a regular elliptic element. A central
element is a scalar matrix `a`, and scalar multiplication by `a ≠ 0` scales the roots of the
characteristic polynomial: `charpoly(a A) = charpoly(A).scaleRoots a`. Irreducibility is
preserved, because scaling by `a⁻¹` recovers the original polynomial and preserves
factorizations of monic polynomials. In characteristic zero the resulting irreducible
polynomial is separable.

## Central translation of character values

`distribution_leftTranslate_of_scalar`: if a group element `z` acts by the scalar `a`, left
translation of a test function by `z` multiplies its integrated action, and hence the
distribution character, by `a`. `hasCharacterValue_mul_left_of_scalar` transports a local
character value `b` at `g` to the local value `a b` at `z g`, using left invariance of Haar
measure. `isLocallyConstant_of_hasCharacterValue`: a function on a subset of the group whose
values are local character values is locally constant, since a local value at one point is
also a local value at every point of the neighbourhood where it holds.

## The descended product

Let `ρ` and `π` be admissible representations of `GL_n(F)` with unitary central characters
`cρ`, `cπ` having the same underlying character, and `Θρ`, `Θπ` their character values on the
regular elliptic set. `ellipticCharacterProduct` is the function on `GL_n(F) ⧸ Z` whose value at
`gZ` is `Θρ(g) conj Θπ(g)` for regular elliptic `g` and `0` otherwise
(`ellipticCharacterProduct_mk`). It is well defined: for central `z`, `zg` is regular elliptic
exactly when `g` is, and the two factors are multiplied by `ω(z)` and `conj ω(z)`, where `ω` is
the common unitary character, so the product is unchanged.

`measurable_ellipticCharacterProduct`: the product is Borel. The image of the regular elliptic
set in the quotient is open (`isOpen_regularElliptic` and openness of the quotient map), the
product is continuous on it (both factors are locally constant), and it vanishes on the
complement.

This is the central descent used for the elliptic pairing in Clozel, *Invariant harmonic
analysis on the Schwartz space of a reductive p-adic group*, §3, Theorem 3, printed
pp. 110–111 (PDF pp. 121–122). Literature ID
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`, SHA-256
`c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
