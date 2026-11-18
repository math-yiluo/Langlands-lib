# Differentials on actual character spaces

Let `r` be a finite matrix representation of an affine group scheme over a
field `k`, and let `chi` be an actual rational character. If `v` belongs to
`r.characterSpace chi`, the tangent matrix of an actual dual-number tangent
point `X` sends `v` to the scalar multiple whose scalar is the epsilon
coefficient of `chi(X)`. The definition `characterTangentScalar chi X`
records that scalar; `tangentMatrix_mulVec_of_mem_characterSpace` proves the
scalar-action formula. Its immediate consequence
`tangentMatrix_mulVec_mem_characterSpace` says that every character space
is stable under every actual tangent matrix.

The proof specializes the published all-algebra character equation
`characterSpace_affine` to the dual numbers, then takes epsilon
coefficients of every coordinate. This is an internal derived helper for
Task 7128's group-side input to the Casimir argument. No smoothness,
characteristic-zero hypothesis, irreducibility or character formula is used.
