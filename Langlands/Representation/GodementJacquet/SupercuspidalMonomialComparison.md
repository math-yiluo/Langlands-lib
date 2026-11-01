# Nonzero monomial comparison of Fourier-regular matrix operators

This internal helper upgrades the explicit conditional Laurent scalar comparison
to one nonzero monomial when the comparison representation is also supercuspidal.
The analytic cross identity remains an explicit premise.

`RankinSelberg.exists_spectralUnit_eq` proves that, for any natural residue
cardinality `q>1`, every complex unit is `spectralUnit(q,s)` for some complex `s`.
The proof uses `s=-log(x)/log(q)`, the positivity of the real logarithm of `q`,
and the complex exponential-logarithm identity. No restriction on the real part
of the resulting parameter is imposed.

`RankinSelberg.exists_monomial_of_laurentEval_ne_zero` proves that a complex
Laurent polynomial whose evaluation is nonzero at every complex unit is
`C(c)*T(k)` with `c` a complex unit and `k` an integer. It clears negative powers
to obtain a polynomial `P`. The nonvanishing assumption forces `P` to be nonzero
and every root of `P` to equal zero. The complex splitting theorem writes `P`
as its leading coefficient times the product of its linear root factors; these
factors are all `X`. Removing the clearing power yields the asserted Laurent
monomial, whose coefficient is the nonzero leading coefficient of `P`.

`fourierRegularMatrixFourierEquiv` restricts the actual plus Fourier transform
with the supplied unitary additive character and scalar self-dual Haar measure
to the existing Fourier-regular matrix-test submodule. Its inverse is the actual
inverse Fourier transform restricted to the same submodule. Existing stability
of both support conditions under the forward and inverse transforms proves that
these maps are well defined. The inherited Fourier inverse identities prove
that this is a complex linear equivalence.

The p-adic results use every prime `p`, the canonical structures of
`PadicField.{uF} p`, rank `m+1` with `m>0`, and a complex representation carrier
in independent universe `uV`. The carrier has only its additive group and complex
module structure. Both operator families act on that same carrier. The character
and additive Haar measure are supplied, together with their self-duality proof.
All regular operators are the existing actual determinant-weighted integrated
operators, and Fourier transforms are the actual plus transforms.

`scalar_ne_zero_of_fourierRegular_comparison` assumes that the carrier is
nontrivial, the original representation `ρ` is smooth, and the comparison
representation `σ` is supercuspidal. At fixed arbitrary complex `s` and `t`, it
assumes the explicit comparison
`Z_σ(t-s,PhiHat)=c • Z_ρ(s,Phi)` for all Fourier-regular tests. It proves `c≠0`.
Indeed, a nonzero input vector has a Fourier-regular test `Psi` with nonzero
constant output under `σ`. The restricted Fourier equivalence supplies an
actual `Phi` with `PhiHat=Psi`. Applying the comparison to `Phi` and that vector
would make the nonzero output zero if `c` vanished. Irreducibility of `σ` is
unnecessary.

`exists_monomial_scalar_of_fourierRegular_cross` assumes an irreducible
supercuspidal `ρ`, a supercuspidal `σ`, an arbitrary complex reflection center
`t`, and the correctly ordered cross identity
`Z_ρ(s,Phi) Z_σ(t-s,PsiHat) = Z_σ(t-s,PhiHat) Z_ρ(s,Psi)`
for every complex `s` and all Fourier-regular tests `Phi,Psi`. It constructs
one complex unit `c` and one integer `k`, independent of both `s` and the test,
such that
`Z_σ(t-s,PhiHat) = (c * spectralPoint(q,s)^k) • Z_ρ(s,Phi)`
for every parameter and test. The earlier Laurent comparison supplies one
Laurent polynomial `A` for all parameters. Irreducibility of `ρ` supplies the
nontriviality of the carrier. The preceding nonvanishing theorem makes every
spectral evaluation of `A` nonzero; spectral surjectivity extends this to every
complex unit. The polynomial factorization argument then identifies `A` with
one nonzero monomial.

The provenance is internal: the proof combines the existing conditional Laurent
comparison, fixed-input nonzero outputs for supercuspidal representations,
Fourier stability and inverse identities, and standard complex polynomial
splitting. It does not prove the analytic cross identity, identify `σ` with any
particular pullback, or extend the comparison to arbitrary full-matrix tests.
Those obligations remain separate from this contribution.
