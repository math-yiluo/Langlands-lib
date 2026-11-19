# Descent of the odd scalar quadratic form

Let `P` be the Hilbert-90 basis for the exact matrix cocycle, `B = P⁻¹`,
and `Q` the split odd matrix. Over the finite Galois splitting field the
matrix `B Q Bᵀ` represents the desired form. Its Galois translate has
alternating difference from it, since `σ(B) = B c(σ)` and `c(σ)` is an
isometry of the full split quadratic form.

The representative that retains the original diagonal entries and
puts each mixed coefficient above the diagonal is unchanged by
alternating differences. This construction commutes with coefficient
maps, so the resulting entries are fixed by every Galois automorphism.
The fixed-field theorem gives a matrix of ground-field coefficients.
Its quotient class is `descendedForm`. Extending this matrix and applying
congruence by `P` recovers the split quadratic class, with the difference
from `Q` certified alternating.

This is an internal construction from the exact cocycle, vector
trivialization and scalar quadratic-form quotient. The calculation
uses no division by two and applies in every characteristic.
