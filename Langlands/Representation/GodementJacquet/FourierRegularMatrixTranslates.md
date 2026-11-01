# Invertible translations of Fourier-regular matrix tests

This is a derived support lemma for the supercuspidal matrix functional-equation
argument. It uses the published actual left-right pullback
`rectangularLeftRightTranslate`, without changing the matrix test space or its
Fourier convention.

The linear map `regularMatrixTranslate A B` pulls a full-matrix test back by
`X ↦ A X B` for arbitrary invertible matrices `A` and `B`. Invertibility of the
two factors preserves singularity, so this restricts to tests vanishing on
singular matrices.

For a canonical p-adic field and a supplied unitary additive character with a
supplied self-dual scalar additive Haar measure, the same pullback preserves
`fourierRegularMatrixTests`. The proof uses the actual rectangular Haar-scaling
theorem and the raw Fourier change of variables. The Fourier argument is
`A⁻ᵀ X B⁻ᵀ`, and its scalar is the actual positive Haar-scaling factor. A singular
`X` yields a singular Fourier argument, where the original Fourier transform is
zero. No determinant-norm-one assumption is imposed on the translations.

`fourierRegularMatrixTranslate` packages this restricted pullback as a complex
linear map. This module proves only preservation of the two support conditions;
it does not assert the matrix functional equation or a gamma factor.
