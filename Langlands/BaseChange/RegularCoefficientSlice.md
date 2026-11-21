# A local slice in characteristic coefficients

Let `F` be a complete nontrivially normed field of characteristic zero. Fix
`γ ∈ GL_n(F)` with separable characteristic polynomial and a positive integer
`l`. The construction gives an open neighborhood of the characteristic
coefficients of `γ` in `F^n` and a continuous perturbation on that neighborhood
with values in `GL_n(F)`.

In a fixed cyclic basis of `γ`, a tuple of characteristic coefficients gives a
companion matrix. Multiplication by the class of `X` in the monic polynomial
quotient identifies its characteristic polynomial. The entries are constant
except for the last column, which consists of the negatives of the input
coefficients. Conjugating back to the original basis gives a continuous family
of matrices that takes the value `γ` at its original coefficients.

Apply the implicit function theorem to the map that conjugates the fixed
matrix times the `l`-th power of a polynomial perturbation of the identity.
The computation of its derivative follows the neighborhood argument in
`NormNeighbourhood`. Write `A` for the matrix of `γ`. To obtain a preimage of a
target matrix `B` at the identity conjugator and zero perturbation, use the
invertibility of `A` to decompose `A⁻¹ B` as `Z A - A Z + ∑ cᵢ A^i`.
The derivative sends the conjugator direction `A Z` and the coefficient
directions `cᵢ/l` to `B`. This gives surjectivity.
Restrict the inverse chart to zero in the kernel coordinate and to the open
locus where both matrix factors are units. Feeding the companion matrices
into this inverse gives a continuous polynomial perturbation, equal to the
identity at the original coefficients. Its `l`-th power times the original
matrix realizes the input coefficients, since the conjugator leaves the
characteristic polynomial unchanged.

This internal construction supplies the local sections in the direct slice
proof of regular transfer (Henniart–Lemaire I.2.5–I.2.8).
