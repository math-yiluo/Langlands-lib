# Compact coefficient smoothing of arbitrary matrix tests

This internal helper uses the actual smooth right representation on full matrix
Schwartz–Bruhat tests and the existing compact coefficient cutoff on determinant
norm one. For a supercuspidal representation `ρ`, a smooth algebraic functional
`ℓ`, a vector `v`, and an arbitrary matrix test `Φ`, it defines
`supercuspidalMatrixSmoothing` as the integrated right action of the inversion
of the restricted cutoff. It is complex linear in `v` and returns an actual
Schwartz–Bruhat test, without a topology on the carrier of `ρ`.

The inverted cutoff for `ρ(a)v` is the left translate by `a` of the inverted
cutoff for `v`, whenever `a` has determinant norm one. The actual integrated
action translation law therefore proves that the smoothed test is translated
on the right by `a`. The supplied plus Fourier transform changes this
covariance to right translation by inverse transpose.

In dimension `m+1` with `0<m`, every singular matrix has a proper conjugate block
unipotent radical fixing it under right inverse transpose. Evaluation of the
smoothed test is a linear functional on the inverse-transpose pullback of `ρ`;
evaluation of its Fourier transform is a linear functional on `ρ`. The proved
covariances make these functionals invariant under the respective radical.
When both representations are supercuspidal, each functional factors through
an actual zero Jacquet quotient, hence vanishes. Thus smoothing sends every
input test into the existing Fourier-regular test submodule, for the supplied
scalar self-dual measure.

The construction and proof are derived here from existing integrated-action,
cutoff, matrix-translation, singular-stabilizer, and Jacquet-quotient helpers.
They do not assert a functional equation, rational continuation, or any spanning
property of the smoothing outputs.
