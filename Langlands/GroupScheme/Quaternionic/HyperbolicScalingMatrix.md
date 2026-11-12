# Matrices for hyperbolic scaling

This internal derived module realizes the hyperbolic scaling maps by explicit
matrices over the division algebra, acting on row vectors. The matrix for the
projection onto the first singular line sends `z` to `h(z,y)x`; the second
projection swaps the pair. For a hyperbolic pair these are idempotent and
orthogonal in both orders.

The matrix `1 + (t-1)P + (t⁻¹-1)Q` acts as the previously constructed scaling
endomorphism. Preservation of all vector values and the extensionality theorem
therefore show that it fixes the actual quotient form under matrix pullback.
Consequently, for every matrix representative of that form, its congruence
defect belongs to the published quadratic kernel. These identities supply the
input to the actual finite-algebra idempotent torus morphism and its factorization
through the isometry group.
