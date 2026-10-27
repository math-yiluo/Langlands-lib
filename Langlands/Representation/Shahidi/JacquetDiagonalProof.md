# Scalar Jacquet covariance under exchanged unipotent diagonal blocks

This module proves the closed
`Langlands.Shahidi.JacquetDiagonalCovarianceStatement`, an internal scalar
prerequisite for the two-block JPSS construction. It uses the published
rectangular subgroup, all-positive block Weyl representative, conjugate Jacquet
kernel, and scalar integrand, with their literal rank conventions. It does not
prove the host `TwoBlockWhittakerExtensionStatement`.

For original block ranks `m+1,n+1`, the first two lemmas show that the last row
of an upper-unipotent matrix fixes a rectangular matrix on the left, and its
first column fixes a rectangular matrix on the right. Each proof expands one
matrix product and retains a single summand; strict lower entries vanish and
the retained diagonal entry is one. Applying these identities to `u₂⁻¹` and
`u₁` fixes the corner `(last n,0)` of `u₂⁻¹ x u₁`. The published
`intertwiningJacquetKernel_eq_neg_corner` then proves invariance of the
negative-corner kernel.

The pointwise covariance proof moves the actual right translating diagonal
blocks through `w u'(x)`. The published `upper_mul_blockSum` gives the coordinate
change `x ↦ u₂⁻¹ x u₁`, and `blockWeyl_conjugate_blockSum` exchanges the two
actual Levi blocks. The element `swapRank (blockSum (u₂,u₁))` only transports
the numerical total rank; its entries are unchanged. Applying the statement's
explicit scalar left-covariance premise to the resulting left factor
`blockSum (u₁,u₂)` gives `z`, and kernel invariance completes the integrand
identity. No covariance of the inducing representations is assumed implicitly.

Two general integral lemmas first work with a supplied measure-preserving
identity for the measurable equivalence `rectangularConj u₂ u₁`.
`integrable_map_equiv` transports the original integrability premise, followed
by multiplication by the constant `z`. `integral_map_equiv` and
`integral_const_mul` give the integral identity. The integral helper has no
integrability premise, as Mathlib's Bochner integral is totalized; this does
not assert convergence for arbitrary group functions. The closed target uses
the helper only in its stated integrable-domain conclusion.

The final theorem discharges measure preservation for every Borel rectangular
additive Haar measure over each p-adic realization. The published
`RankinSelberg.unipotent_det` gives determinant one for both blocks, so their
`determinantNorm` values are one. Substitution into
`map_rectangularConj_padic` makes its determinant scaling factor one. The
pointwise and integral lemmas then assemble the exact target, with independent
field and coefficient universes.

The scalar left-covariance law and integrability premise remain explicit in the
proved statement. Construction of cell sections, covariance from actual
inducing Whittaker functionals, full upper-unipotent covariance, and the final
coefficient/Fourier assembly remain separate obligations. No topology on the
coefficient module or additional measure normalization is required here.
