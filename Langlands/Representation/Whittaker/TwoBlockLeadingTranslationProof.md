# Proof of leading-block translation on the cell submodule

`Langlands.Whittaker.twoBlockLeadingTranslation` proves
`TwoBlockLeadingTranslationStatement`. The proof first establishes the cell-point identity for arbitrary exchanged diagonal
blocks using the existing radical multiplication and block Weyl conjugation
identities. For `diag(g,I_A)` the rectangular coordinate becomes `g⁻¹ x`
and the original-order Levi element is `diag(I_A,g)`.

The factorization preserves the cell. Applying it also to `g⁻¹` shows that
the right translate of a function supported in the cell is supported there.
The translated restriction is the original restriction composed with the
continuous affine homeomorphism `x ↦ g⁻¹ x`, then postcomposed with the actual
inducing linear action. Both operations preserve compact support.

The final pointwise equality uses the actual canonical normalized induction
covariance and the Levi-section projection identity. The square-root modulus
in that law equals the existing positive `leviHalfModulus` in the statement.
No scalar integral or Fourier argument is used.
