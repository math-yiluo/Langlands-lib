# Quadratic forms descended from orthogonal matrix cocycles

This internal construction descends a symmetric nondegenerate Gram matrix twisted
by an orthogonal matrix cocycle over a finite Galois field extension `L/k`.
It uses the published matrix Hilbert 90 theorem in `GaloisVectorDescent`.
It does not assert any local-to-global arithmetic principle.

`OrthogonalCocycle H` is a function `c : Gal(L/k) → GL(n,L)` with `c(1) = 1`,
the crossed cocycle law `c(στ) = c(σ) σ(c(τ))`, and the isometry condition
`c(σ) H c(σ)ᵀ = H` after extending the entries of `H` from `k` to `L`.
The finite coordinate type `n` may be empty and may lie in any universe.

For symmetric invertible `H`, `nonempty_descent` proves that `Descent c` is
inhabited. Its data consist of a symmetric invertible matrix `B` over `k` and an
invertible matrix `P` over `L` satisfying

`c(σ) = P σ(P⁻¹)` and `B_L = P⁻¹ H_L (P⁻¹)ᵀ`.

`descent` chooses these data without imposing additional hypotheses. No
uniqueness or canonical choice is asserted.

The proof applies matrix Hilbert 90 to the full finite automorphism group.
Its trivializing matrix `P` gives `σ(P⁻¹) = P⁻¹ c(σ)`. Substituting this into
`σ(P⁻¹ H_L (P⁻¹)ᵀ)` and applying the isometry condition shows that this Gram
matrix is fixed by every automorphism. The supporting
`exists_matrix_of_fixed` uses the finite-Galois fixed-field theorem entry by
entry to obtain `B`. Transposition shows that `B` is symmetric, using
injectivity of the field inclusion. The Gram matrix over `L` is invertible
as a product of invertible matrices. Its determinant is the image of `det B`,
so `B` is invertible as well.

Provenance is internal: the construction combines the published
`Langlands.LinearAlgebra.GaloisVectorDescent.exists_matrix_coboundary'` with
Mathlib's finite-Galois fixed-field theorem and matrix identities. The equations
record all data needed for the comparison between orthogonal cocycles and
quadratic forms in `OrthogonalCocycleComparison`. This module does not construct
such a cocycle from a
group-scheme cocycle or compare its localizations.
