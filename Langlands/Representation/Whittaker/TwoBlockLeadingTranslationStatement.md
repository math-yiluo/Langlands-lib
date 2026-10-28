# Leading-block translation of two-block cell vectors

`TwoBlockLeadingTranslationStatement` concerns the actual canonical ordered
normalized induction in ranks `A = a + 1` and `B = b + 1`. For every
`g ∈ GL_B`, its leading embedding in the exchanged order is the entry-preserving
rank transport of `diag(g,I_A)`. Right translation by this element preserves
the cell submodule.

On the rectangular restriction, the translated vector at `x` equals the
original restriction at `g⁻¹ x`, acted on by the original-order tensor Levi
element `diag(I_A,g)` and multiplied by its positive half modulus. The
statement retains the existing `leviHalfModulus` normalization rather than
replacing it with an unproved real-power expression. It applies to arbitrary
factor representations and every actual cell vector.

This is an internal algebraic and support prerequisite for the JPSS extension
calculation. The block Weyl identity moves `diag(g,I_A)` across the cell
representative, giving `diag(I_A,g) w n(g⁻¹ x)`. Actual normalized covariance
gives the stated action. The corresponding invertible rectangular coordinate
change is a homeomorphism, which preserves compact support, and the same
factorization preserves support in the cell.

This proposition definition supplies no proof, scalar integral formula or
prescribed Whittaker coefficient.
