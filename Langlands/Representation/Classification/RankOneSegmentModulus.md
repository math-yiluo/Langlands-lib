# Half-modulus cancellation for a rank-one segment

This internal calculation derives directly from the Library's actual upper
block modulus formula. `rankOneSegmentCharacter` is the determinant character
`ν^((m-1)/2) (χ ∘ det)` on `GL_(m*1)`. For `m` blocks of size one, multiplication of the positive
half-modulus by the determinant-norm characters with exponents `0, …, m-1`
leaves the product of the determinant-norm characters with the common exponent
`(m-1)/2`.

The proof counts the factors above and below each diagonal block, obtaining
exponents `m-1-i` and `i` in the full modulus. Positive real powers then divide
these exponents by two and cancel the varying induction twists. This is an
algebraic normalization identity; it asserts no constituent or generation
theorem.
