# The complex local Tate functional equation

This module proves `Langlands.LocalFactor.ComplexArchimedeanTateStatement` as
`Langlands.LocalFactor.ComplexTate.complexArchimedeanTateStatement`.
The proof uses the
statement's measure of twice Lebesgue area, its positive trace Fourier
kernel and its spectral variable `u = s + t`. [Statement](Statement.md)

## Convergence and the common strip

`integrable_integrand` uses boundedness of the Schwartz function near the
origin, local integrability of the radial power with exponent `2 * Re(u) - 2`,
and Schwartz decay at infinity. `analyticAt_zeta` follows by differentiating
under the integral on `Re(u) > 0`. The derivative's logarithm is bounded
using integrands at two nearby spectral parameters in the convergence
half-plane. [Zeta integrals](ComplexTateZeta.md)

`tate_identity` uses the determinant of multiplication by a complex number
and the symmetry of the trace kernel to relate the products of zeta
integrals for two Schwartz functions on `0 < Re(u) < 1`. Take the second
function to be the angular Gaussian of weight `m`. Its zeta integral is
`Γℂ(u + |m|/2)` and its transform is `i^|m|` times the Gaussian of weight
`-m`. The transformed Gaussian therefore gives
`i^|m| Γℂ(1 - u + |m|/2)` at the reflected parameters. Substitution in
`tate_identity` gives `zeta_fourier_mul_Gammaℂ`. The Schwartz witness and
both Gaussian evaluations also supply the last conjunct of the statement.
[Trace Fourier transform](ComplexTateIdentity.md) · [Angular Gaussians](ComplexTateGaussian.md)

## Continuation and the scaled equation

On `Re(u) < 1`, `reflectedZeta` uses the convergent zeta integral of the
Fourier transform at `(-m, 1 - u)` multiplied by
`Γℂ(u + |m|/2) / (i^|m| Γℂ(1 - u + |m|/2))`. This formula is
meromorphic because the reciprocal of `Γℂ` is entire. The common-strip
identity and the nonvanishing of `Γℂ` at positive real part show that
the formula agrees with the original integral on the overlap.
`gluedZeta` thus defines a meromorphic function everywhere. `extension`
takes its Mathlib meromorphic normal form after the translation `s ↦ s + t`.
Analyticity on `0 < Re(s + t)` ensures those values agree with the integral.
Uniqueness follows from `RealTate.eq_of_meromorphicNFOn` on that open
half-plane. [Meromorphic identity theorem](RealTateProof.md)

`scaledFourier` composes the basic Fourier transform with multiplication by
`a` and scales its values by `c`, giving the Schwartz witness for the
specified integral. At angular weight `-m` and parameter `1 - u`, its zeta
integral acquires the factor `c * (a / ‖a‖)^m * ‖a‖^(2 * (u - 1))`.
On the common strip this factor and `zeta_fourier_mul_Gammaℂ` give the
normalized equation, with the additional multiplier `i^|m|`. Both sides
are meromorphic on the plane. `RealTate.eventuallyEq_nhdsNE_of_eqOn`
extends their equality on the open strip to equality on a punctured
neighbourhood of each point. The argument holds for every `c : NNReal`.
[Trace Fourier transform and dilation](ComplexTateIdentity.md)

## Provenance

Tate's *Fourier analysis in number fields and Hecke's zeta-functions*
(`tate-1967-thesis`) gives differentiation under the integral in Lemma
2.4.1, the common-strip identity in Lemma 2.4.2 and the local functional
equation in Theorem 2.4.1, printed pp. 313–315. The complex case of §2.5,
printed pp. 318–319, gives the angular Gaussians, their Fourier transforms
and the polar zeta integral. Dividing Tate's Gaussian by `π` turns its
zeta integral into Mathlib's `Γℂ`, including the factor of two. The Lean
proof implements continuation by gluing and meromorphic normalization
using the identity theorem from the published real-place proof.
[Source and normalization details](Statement.md)
