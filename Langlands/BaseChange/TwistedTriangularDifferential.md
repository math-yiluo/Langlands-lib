# Surjectivity in the upper triangular twisted conjugation map

`TwistedTriangularDifferentialStatement` gives the surjectivity of
`(X,Y) ↦ X − T(X) + T(Y)`, where `T(X) = δ σ(X) δ⁻¹`. The source is the
product of the full and upper triangular matrix spaces over a reduced,
finite-dimensional commutative algebra `E` over a characteristic-zero
field `F`. The parameter is σ-regular for an exponent `l` with `σ^l = 1`.
This linear map is the right-translated differential of
`(k,p) ↦ k δ σ(k)⁻¹ σ(p)` at `(1,1)`.

The proof uses the pairing `Tr_{E/F}(tr(ZX))`. To see why the scalar trace
pairing is nondegenerate, use the product of the residue fields of the
reduced Artinian ring `E`. For each `a`, take `b` with coordinates inverse
to the nonzero coordinates of `a` and zero elsewhere. Then `ab` is
idempotent. If `a` annihilates the scalar trace pairing, left
multiplication by `ab` is an idempotent of trace zero. In characteristic
zero it vanishes, so `ab = 0` and hence `a = 0`. Testing the matrix pairing
on single-entry matrices proves its nondegeneracy. The matrix trace is
cyclic and the scalar trace is invariant under `σ`, so `T` preserves
the pairing.

An element `Z` corresponding to an annihilator of the differential first
satisfies `T(Z) = Z`, by testing the full matrix directions and using the
pairing invariance. Testing the upper triangular directions then makes
`Z` strictly upper triangular. The proof bounds the possible entries
of each matrix power and deduces that `Z` is nilpotent.

Iterating `T(Z) = Z` shows that `Z` commutes with the cyclic norm.
Conjugate the norm and `Z` by the association witness. In every residue
field of `E`, extend scalars to an algebraic closure. The resulting
regular norm has separable characteristic polynomial. Cayley–Hamilton
gives semisimplicity, and separability bounds each eigenspace dimension
by one. A commuting nilpotent preserves each eigenspace and vanishes on
it. Thus the conjugated matrix vanishes after extension and in each
residue field, and consequently vanishes over `E`. The dual annihilator
of the differential is zero, which proves surjectivity.

This is an internal derivation using the trace-pairing method of
Henniart–Lemaire (2011), I.2.7, Lemma 1, printed page 19. The upper
triangular directions are chosen for the compact averaging argument of
Harish-Chandra (1981), §§3–4.
