# Orthogonal cocycle comparison after scalar extension

Let `L/F` be finite Galois, `K/F` a field extension, and `R = K ⊗[F] L`.
`tensorGaloisMap` acts by each automorphism of `L/F` in the second factor
and fixes `K`. `exists_tensor_fixed_preimage` proves that a coefficient in
`R` fixed by these maps comes from `K`. It expands the tensor in an
`F`-basis of `K`, uses the fixed-field theorem on its finitely many
coefficients in `L`, and takes the resulting linear combination in `K`.
`exists_unit_of_tensor_fixed` applies this entrywise to an invertible
matrix and reflects a nonzero determinant to `K`.

`gramCongruent_of_tensorCohomology` considers two orthogonal matrix
cocycles on `L/F` for the same Gram matrix `H`. Each comes with a descended
Gram matrix `Bᵢ` over `F` and a Hilbert 90 matrix `Pᵢ` over `L`. Suppose an
invertible matrix `a` over `R` preserves the image of `H` and satisfies
`c₂(σ) = a⁻¹ c₁(σ) σ(a)` after mapping the cocycle values into `R`. Then
`P₁⁻¹ a P₂` in `GLₙ(R)` is fixed by every tensor Galois map. Its descent to
`GLₙ(K)` is a congruence between the images of `B₂` and `B₁` in `K`. This
follows from the Gram identities after embedding `K` into `R`, whose
injectivity reflects the resulting matrix equality.

This internal comparison extends the matrix cohomology and Gram
descent calculation to arbitrary extension fields `K`, including
completions. The tensor ring may have zero divisors.
