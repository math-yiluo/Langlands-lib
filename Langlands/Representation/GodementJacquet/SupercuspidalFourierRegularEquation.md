# Supercuspidal equation on Fourier-regular matrix tests

This internal helper proves the actual monomial functional equation on the
Fourier-regular matrix-test subspace. Fix any prime, a p-adic field `F` in
universe `uF` with its canonical structures, matrix size `d=m+1`, and a complex
representation on an independent carrier in universe `uV`. The carrier has
only an additive group and complex module structure. Supply a unitary additive
character `psi`, an additive Haar measure `nu`, and a proof of its self-duality.
The group measure is the existing canonical normalized GL Haar measure; the
Fourier transform uses the exact square product of `nu`.

`fourierRegularInverseTransposeZetaOperator` is a complex linear map from the
existing Fourier-regular matrix-test subspace to endomorphisms of the carrier.
For a smooth inverse-transpose pullback of `rho`, it sends `Phi` at parameter
`s` to the actual regular zeta operator for `rho.comp inverseTranspose`, at
`d-s`, applied to the actual plus Fourier transform of `Phi`. The definition
composes the restricted Fourier equivalence with the existing restricted zeta
operator. The application lemma exposes this literal formula. Both `Phi`
and its transform vanish on singular matrices.

`exists_monomial_fourierRegular_inverseTranspose` assumes `m>0`, supercuspidality
and irreducibility of `rho`. It produces one complex unit `c` and one integer
`k`, independent of parameter and test, such that for all complex `s` and all
Fourier-regular tests,

```text
Z_(rho.comp inverseTranspose)(d-s, PhiHat)
  = (c * spectralPoint(q,s)^k) • Z_rho(s,Phi).
```

There is no cross-identity premise. Inverse transpose preserves the actual
supercuspidal predicate by the existing direct Jacquet-quotient transport.
The actual convolution exchange gives
`D(Phi) A(Psi) = A(Phi) D(Psi)`. Symmetry puts it in the order required by the
nonzero monomial comparison theorem. Applying that theorem with comparison
representation `rho.comp inverseTranspose` and reflection center `d` gives
the claimed unit and integer. The rank is at least two; the two universes
remain independent.

`matrixIntegral_eq_of_fourierRegular_inverseTranspose` evaluates any such
operator equality on a vector and an arbitrary algebraic complex functional.
The result is the literal scalar equation
`Z(PhiHat,d-s,g ↦ ell(rho(inverseTranspose(g))v))
 = a * Z(Phi,s,g ↦ ell(rho(g)v))`.
It uses the already proved evaluation of the actual compact operators as matrix
integrals and complex linearity of the functional. This evaluation result only
requires smoothness of the two representations, a Fourier-regular test, and
the displayed operator equality at the chosen parameter.

The provenance is internal: the proof composes the existing actual convolution
exchange, direct inverse-transpose transport, nonzero monomial comparison, and
operator evaluation. This contribution does not extend the equation to arbitrary
full-matrix tests or assemble the closed normalized functional-equation data.
