# Laurent model of the constructed rank-one epsilon expression

Worker 20 constructs an actual Laurent polynomial and its rational-function
image from the published convergent rank-one Gauss expression. The new module
is `Langlands.LocalFactor.Abelian.Laurent`; all its public names are in
`Langlands.LocalFactor.PadicAbelian`, beside the imported constructors.

## Inputs and definitions

The inputs are an arbitrary prime `p`, finite p-adic extension `F` with
arbitrary carrier universe, supplied `T : F.TopologicalData`, continuous
quasicharacter `χ`, nontrivial unitary additive character `ψ`, and regular
additive Haar measure `μ`. The topology and Borel measurable space are
precisely those of `T`. The notation `LocalHaar` expands the published measure
bundle; it does not introduce a second structure.

Write `a = T.multiplicativeConductor χ`, `n = T.additiveConductor ψ`,
`q = T.residueCardinality`, and `c = deligneConstant T χ ψ μ.measure`.
These are actual constructed conductors, the actual residue cardinality,
and the published unshifted measure-dependent Gauss constant.

The declarations implement the following objects:

| Declaration | Meaning |
| --- | --- |
| `epsilonExponent` | The integer `d = a + n`; the additive conductor may be negative. |
| `epsilonLaurent` | The Laurent polynomial `C(c) * T(d)` in `LaurentPolynomial ℂ`. |
| `epsilonLaurentValue` | Its ring-homomorphism evaluation at a supplied `t : ℂˣ`. |
| `rationalEpsilon` | Its image in `RatFunc ℂ` under the Laurent ring homomorphism sending the variable to the nonzero rational function `X`. |

`epsilonLaurentValue_eq` and `rationalEpsilon_eq` prove the respective
formulas `c * t^d` and `C(c) * X^d`. This is a single Laurent monomial,
possibly with zero coefficient. `rationalEpsilon_ne_zero_iff` proves that
the rational object is nonzero exactly when the constructed Gauss constant
is nonzero. No nonvanishing assumption is introduced.

The general Laurent evaluation is only exposed at nonzero variables.
Negative exponents therefore retain a possible pole at `X = 0` in the
rational model. No totalized rational-function evaluation is presented as an
analytic value at a pole. Spectral evaluation is valid for every finite
complex `s`, because `spectralVariable_ne_zero` proves
`exp(-s * log q) ≠ 0`.

## Construction identities and implemented proofs

`epsilon_eq_constant_mul_spectral_pow` proves

```
epsilon T χ ψ μ.measure s
  = deligneConstant T χ ψ μ.measure
      * spectralVariable T s ^ epsilonExponent T χ ψ.
```

The proof unfolds the already constructed expression and separates the
unramified and ramified cases using the actual multiplicative conductor.
In the unramified case the formula is
`χ(π)^n * exp(n * (1-s) * log q) * vol(O)`. Splitting the exponential
isolates its value at zero and the factor `exp(-s * log q)^n`.

In the ramified case the integration shell has order `-(n+a)`.
The imported `gaussIntegrand_on_shell` makes the spectral factor constant
on that shell. Its measurability follows from the imported equality with
the closed valuation shell. The proof pulls the constant through the
set integral, identifies the zero-parameter integrand, and rewrites
`log(q^(n+a))` by `Real.log_zpow`. The imported
`gaussIntegrand_integrable` already proves absolute integrability of this
compact-shell expression for each complex parameter and actual Haar
measure. There is no reliance on a nonintegrable integral's fallback value.
The private `spectralVariable_zpow` uses the real logarithm and complex
exponential integer-power identities; ring normalization reconciles the
integer-exponent arithmetic.

`epsilonLaurentValue_spectral` then identifies Laurent evaluation at the
unit associated to `spectralVariable T s` with `epsilon T χ ψ μ.measure s`.
The proof uses the preceding monomial identity and the Laurent evaluation
formula. These identities justify the Laurent construction directly from
the published expression; they do not invoke the local functional equation.

The rational nonvanishing equivalence uses the injectivity of `RatFunc.C`,
the nonzero rational variable `RatFunc.X`, and preservation of nonvanishing
under integer powers. It deliberately leaves nonvanishing of the actual
coefficient to the separate abelian theorem.

## Original source and derived provenance

Tate, *Number theoretic background* (1979), section 3.2.6, printed
pages 13–14 / retained Corvallis Part II PDF pages 22–23, defines both
conductors and gives the unramified formula (3.2.6.1), the ramified shell
integral (3.2.6.2), and the unramified-twist relation (3.2.6.3).
The original pages were read as text and visually checked for the signs,
the valuation of the shell, and the exponent `n(ψ)+a(χ)`.
The retained source is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
registered as `tate-1979-number-theoretic-background`, with verified SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
No source-specific erratum was found in the project notes or literature.

The Laurent and rational packaging is derived content: it represents the
already published formulas in standard Mathlib rings and proves the
evaluation identity from those formulas. It does not claim a new proof of
Tate's arbitrary-unramified-twist theorem. Its coefficient retains the
unshifted Deligne convention and the supplied Haar measure. It does not
choose a self-dual measure, shift to Langlands' centered constant, assert
nonabelian epsilon existence, or identify any reciprocity map.

The only project import is the published canonical
`Langlands.LocalFactor.Abelian.Padic`, which supplies the actual Gauss
expression, conductor and shell identifications, convergence, and its
comparison with `T.abelianEpsilonExpression`. The added Mathlib import is
`Mathlib.Algebra.Polynomial.Laurent` from the prepared environment. The
published dependencies are reused unchanged; the new code and exposition
are by Worker 20.
