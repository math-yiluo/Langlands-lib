# Laurent dependence of a Fourier-regular scalar comparison

This derived helper works over every prime `p` and canonical
`PadicField.{uF} p`. Its topology, valuation, local-field structure and
normalized determinant absolute value are the canonical ones. Its complex
representation carrier belongs to independent universe `uV` and needs only an
additive commutative group and complex module structure. No topology on the
carrier is imposed.

`determinantWeight_sub_spectral` gives the exact unshifted identity
`|det(g)|^(t-s) = |det(g)|^t * spectralPoint(q,s)^(-ord(det(g)))`, with
`q` the canonical residue cardinality. The fixed complex number `t` is arbitrary;
in the matrix functional equation it can be specialized to the matrix size.
The sign in the integer exponent follows from the convention
`spectralPoint(q,s) = q^(-s)`.

For every smooth representation `σ`, regular full-matrix test `Φ`, vector `v`
and algebraic functional `ℓ`,
`exists_laurent_regularMatrixZetaOperator_dual_sub` constructs one Laurent
polynomial `A` such that `ℓ(Z_σ(t-s,Φ)v)` equals its evaluation at
`spectralPoint(q,s)` for every complex `s`. Regularity means the actual test
vanishes on singular matrices, so its restriction to GL has compact support.
Smoothness makes `g ↦ ℓ(σ(g)v)` locally constant even for an arbitrary algebraic
functional. The integrand with the fixed weight at `t` is continuous and
compactly supported. The existing finite discrete-order integral theorem,
applied to the continuous integer function `-ord(det(g))`, supplies the Laurent
polynomial. The actual operator evaluation theorem identifies the scalar
integral with the functional evaluation above.

`regularMatrixZetaEvaluationLaurent` chooses such a polynomial and
`regularMatrixZetaEvaluationLaurent_spec` records its all-parameter evaluation
identity. This choice is independent of `s`.

`exists_laurent_scalar_of_fourierRegular_cross` assumes rank `m+1` with `m>0`,
an irreducible supercuspidal representation `ρ`, an arbitrary smooth
representation `σ` on the same carrier, a supplied unitary nontrivial continuous
additive character `ψ`, a supplied additive Haar measure `ν` and a proof of its
self-duality. For the actual plus Fourier transform `ΦHat`, its explicit premise
is the cross identity
`Z_ρ(s,Φ) * Z_σ(t-s,ΨHat) = Z_σ(t-s,ΦHat) * Z_ρ(s,Ψ)`
for all complex `s` and Fourier-regular tests `Φ,Ψ`. Fourier regularity means both
the test and its actual plus transform vanish on singular matrices.

Under that premise the theorem constructs one Laurent polynomial `A` satisfying
`Z_σ(t-s,ΦHat) = laurentEval(spectralUnit(q,s),A) • Z_ρ(s,Φ)`
for every `s` and every Fourier-regular test `Φ`. The existing conditional
operator-comparison theorem supplies a scalar separately at each `s`. To identify
all of them with one Laurent polynomial, the proof fixes a nonzero input `v`,
a Fourier-regular test `Φ₀` with constant nonzero output `u` under `Z_ρ`, and a
smooth functional with `ℓ(u)≠0`. Evaluating the comparison for `Φ₀` by that
functional makes the scalar equal to the Laurent polynomial of the reflected
Fourier integral divided by the fixed number `ℓ(u)`. This fixed quotient gives
the asserted single Laurent polynomial for all tests and parameters.

The provenance is internal: the proof combines the actual regular zeta operator,
its arbitrary-functional integral identity, the finite determinant-order Laurent
integral theorem, the existing constant-output construction and the conditional
scalar comparison. It does not prove the cross identity for any particular `σ`.
It does not assert that `A` is nonzero or a monomial, nor establish a functional
equation on arbitrary full-matrix tests. Those remain separate obligations.
