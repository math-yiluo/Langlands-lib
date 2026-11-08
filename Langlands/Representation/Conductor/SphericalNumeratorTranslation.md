# Central translation of actual finite spherical numerators

This internal unit propagates the actual integrated central-translation identity
to Laurent series, denominator products and finite numerators. For an integer
`t`, let `Aₜ` be the central translation factor, `wₜ` the actual translated model
vector, and `S(w)` its actual spherical Laurent series. Then

`S(wₜ) = single(-(n + 1)t, Aₜ) * S(w)`.

Equality follows coefficient by coefficient from the integrated formula.
Associativity gives the same formula for the product with the fixed coordinate
denominator of any scalar polynomial `P`.

The unit proves directly that multiplying a finite Laurent series by one
monomial preserves finite support, and that the sum of its coefficients is
multiplied by the monomial coefficient. The proof sums over the translated
original support, allowing cancellation to shrink the actual resulting support.
Consequently central translation preserves membership in the finite-support
model subspace, and its actual numerator is multiplied by `Aₜ`.

`corankOneFiniteSupportCentralTranslate` packages this action as a complex linear
endomorphism of `corankOneFiniteSupportModelVectors` for the chosen polynomial
`P`. Its underlying vector is the original central model translate, its
membership proof is the finite-support preservation just proved, and its
linearity follows by restricting the original model action. The actual numerator
linear map intertwines this endomorphism with multiplication by `Aₜ`.

Every actual finite numerator therefore remains an actual finite numerator
after multiplication by any integral power of the symmetric coordinate-product
unit. To remove the inverse scalar determinant weight in `Aₜ`, the proof uses
the complex vector-subspace property of the actual numerator image and the
proved nonvanishing of the determinant weight. This is a statement about that
actual image, not an assumption of ideal stability.

All results concern arbitrary nonarchimedean local fields with the existing
Jacquet normalization and smooth models, at independent field and vector-space
universes. They are internal deductions from the actual coefficient identity,
finite sums and model linearity. Full stability under symmetric Laurent
polynomials, universal finite denominator products, the constant numerator one,
and the essential-conductor target remain separate obligations.
