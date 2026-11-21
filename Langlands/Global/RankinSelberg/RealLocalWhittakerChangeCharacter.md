# Change of character in the real uniform Whittaker model

`RealCharacterChange.changeDiagonal r a` is the diagonal matrix with entries
`a^r, a^(r-1), …, 1` in `GL_(r+1)(ℝ)`. Every invertible diagonal normalizes
upper unitriangular matrices. For this diagonal `A`, the ratio of consecutive
entries is `a`, so `A⁻¹ u A` has simple-root entries `a⁻¹` times those of `u`.
`changeDiagonal_character` uses this on the sum of simple-root entries: the
existing character with parameter `b` on `A⁻¹ u A` equals the character with
parameter `b * a⁻¹` on `u`. This uses the Library's additive phase unchanged.

`leftTranslate x` is the complex-linear map `W ↦ (g ↦ W (x * g))`.
`leftTranslate_isIntertwiner` composes a generating coefficient map with
`leftTranslate A⁻¹`. The unipotent covariance follows by conjugation;
smoothness follows by composition with smooth multiplication. Associativity
makes the translation commute with the right compact action and with the
right derivative, which is taken at the identity in the right variable.
The square-Frobenius formulas for the matrix and its inverse give
`height(x*y) ≤ height(x) height(y)`: apply submultiplicativity to each of the
two norms and use the nonnegative cross terms in the product. Thus a bound
with common exponent `N` retains that exponent and replaces each vector's
constant `C` by `C * height(A⁻¹)^N`. The translated map is still uniform in
the source vectors in precisely the sense of `IsRealUniformWhittakerIntertwiner`.
`leftTranslate_mem_model` extends the inclusion from each range to their
submodule supremum via the comap of the translation.

This is an internal normalization construction on the specified real
coefficient space. The proof adapts the left-diagonal argument of
`ComplexLocalWhittakerChangeCharacter` to real characters and to the stronger
uniform growth quantifier. It assumes no continuous-model comparison,
noncompact right-translation stability, or analytic continuation result. It
does not prove the local functional equation.
