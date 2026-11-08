# Actual simple-root degree bounds for the canonical induced space

This is derived supporting work by Worker 669. It specializes the actual
rank-one curve construction and degree theorem to the fixed linked maps of a
supplied split pinning. The all-test covariance premises are discharged by
membership in the entire canonical induced coordinate subspace.

For a supplied split pinning `p`, a simple-root index `r`, and a rational point
`g` of the original affine group, `p.linkedNegativeSimpleCurvePolynomial r g`
is an algebra homomorphism from the actual coordinate algebra of the group to
`k[X]`. It is the existing `curvePolynomial` applied to the actual curve
`s ↦ xm(s) g`, where `xm` is the negative map of the fixed
`p.linkedRootParametrization r`. Thus it pulls back regular coordinates along
an actual scheme morphism. It does not interpolate rational values. Its
underlying curve and polynomial construction have the coefficient-algebra
evaluation compatibility proved in `RankOneCovariantCutoff`.

Assume in addition that the field is infinite, the root index is finitely
enumerated, and the integral coroot span is the full cocharacter lattice.
`natDegree_linkedNegativeSimpleCurvePolynomial_le` says that every coordinate
`f` in `p.canonicalRhoCovariantSubspace hspan m` has polynomial degree at most
`m` on this curve, for each simple root and every rational point `g`. Here the
subspace is the entire left-covariant subspace of the original affine
coordinate algebra at the actual polarized-rho parabolic and the m-th power
of its extended negative-rho character. The natural number `m` may be zero.

The linked root package supplies the literal rank-one relation on every
relative test scheme. A simple root is positive, so
`canonicalRhoCovariantSubspace_left_linkedPositive` supplies its all-test left
invariance for every member of the subspace. The corresponding
`canonicalRhoCovariantSubspace_left_simpleCoroot` supplies the all-test
multiplier `(z⁻¹)^m`. Applying `natDegree_negativeCurve_le` with these data
proves the degree bound; no covariance or degree premise remains supplied.

The field universe and characteristic are arbitrary. The degree conclusion
is for curves through rational points over the given infinite field. No bound
at arbitrary coefficient-algebra translates is asserted. The pinning and full
integral coroot-span hypothesis remain supplied. This module proves no
Frobenius cutoff, entire-space dimension or irreducibility, highest-weight
existence, or `SteinbergBigCellStatement`.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
