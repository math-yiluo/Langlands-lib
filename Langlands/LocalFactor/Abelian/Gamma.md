# Direct abelian gamma on the common regular domain

Worker 20 constructs the direct fixed-Haar abelian expression

```
gamma(s,χ,ψ,μ) = epsilon(s,χ,ψ,μ) * L(1-s,χ⁻¹) / L(s,χ)
```

from the published convergent Gauss epsilon and regular L-value constructions.
The module is `Langlands.LocalFactor.Abelian.Gamma`. It supplies the common
regular domain, its actual values, coefficient and nonvanishing identities,
and compatibility under an actual p-adic algebra equivalence. No local
functional equation or nonabelian constant system is used.

## Inputs and evaluation domain

The first namespace is `Langlands.LocalFactor.PadicAbelian`. Its inputs are
a prime `p`, a finite p-adic field `F` in an arbitrary carrier universe,
supplied `T : F.TopologicalData`, a continuous quasicharacter `χ`, a nontrivial
unitary additive character `ψ`, and a regular additive Haar measure `μ`.
All character and measure types use exactly `T.topology` and its Borel
measurable space. The local notations reuse the published bundles.
The inverse `χ⁻¹` is pointwise inversion in the existing group of continuous
homomorphisms; no dual-character structure is introduced.

Write `q = T.residueCardinality`, `t(s) = exp(-s * log q)`, and
`Pχ = lPolynomial T χ`. The polynomial is the published Euler denominator
with constant coefficient one. The new declarations are:

| Declaration | Construction |
| --- | --- |
| `GammaRegularAt T χ s` | Conjunction of the existing `RegularPoint` predicates for `χ` at `s` and `χ⁻¹` at `1-s`, each with its actual multiplicative conductor. |
| `GammaRegularPoint T χ` | Subtype of complex numbers satisfying that conjunction. |
| `gammaLRatio T χ s` | The unit `regularLValue(χ⁻¹,1-s) / regularLValue(χ,s)`. |
| `gammaValue T χ ψ μ s` | The actual `epsilon T χ ψ μ.measure s.val` multiplied by that unit's complex value. |

`gammaRegularAt_iff_polynomial_ne_zero` identifies the predicate with

```
Pχ.eval (t(s)) ≠ 0 ∧ Pχ⁻¹.eval (t(1-s)) ≠ 0.
```

Thus neither occurrence of `regularLValue` evaluates an L-factor at a pole.
The domain is the common regular domain of the two individual L-factors,
and need not be the maximal regular domain after cancellation in their ratio.
No value outside this subtype is assigned. The imported `rationalLFactor`
continues to represent the individual factors with their poles retained.

The ratio is unit-valued because both L evaluations are units. Gamma itself
is complex-valued: the Gauss coefficient's nonvanishing has not been proved
by this construction. In particular, this definition does not obtain a unit
by silently assuming a separate abelian theorem.

## Formulas and implemented construction proofs

`coe_gammaLRatio` identifies its scalar value with
`lFactor T χ⁻¹ (1-s.val) / lFactor T χ s.val`. Although `lFactor` is a
totalized raw expression in the imported API, this identity is asserted only
on `GammaRegularPoint`; the domain proofs exclude the problematic values.
The proof uses `coe_regularLValue` and compatibility of coercion with division.

`gammaLRatio_eq_polynomial_ratio` proves the more explicit identity

```
(gammaLRatio T χ s : ℂ) = Pχ.eval (t(s.val)) / Pχ⁻¹.eval (t(1-s.val)).
```

It unfolds the two unit-valued reciprocal evaluations and applies
`inv_div_inv`. The original polynomial is in the numerator, and the reflected
inverse-character polynomial is in the denominator.
`gammaValue_formula` follows by substituting `coe_gammaLRatio`.

Let `a = T.multiplicativeConductor χ`, `n = T.additiveConductor ψ`, and
`c = deligneConstant T χ ψ μ.measure`. The theorem
`gammaValue_eq_constant_mul_spectral_pow` proves

```
gammaValue T χ ψ μ s =
  c * t(s.val)^(a+n) * (Pχ.eval (t(s.val)) / Pχ⁻¹.eval (t(1-s.val))).
```

Here `a+n` is the existing integer `epsilonExponent`, so negative additive
conductors remain possible. The proof substitutes the published
`epsilon_eq_constant_mul_spectral_pow` from `Abelian.Laurent` and the
polynomial ratio identity. That imported epsilon identity is already proved
from the convergent Gauss expression, including its unramified branch;
`Padic.gaussIntegrand_integrable` establishes convergence of the ramified
compact-shell integral for every complex argument. No totalized
nonintegrable integral is being used as an analytic value.

`gammaValue_ne_zero_iff_epsilon` removes the nonzero unit ratio from the
product. `gammaValue_ne_zero_iff_constant` then uses the imported epsilon
monomial identity and `spectralVariable_ne_zero`: a complex exponential
and any of its integer powers are nonzero. These are equivalences with
nonvanishing of the actual epsilon or actual coefficient, respectively;
neither theorem proves that coefficient nonzero.

## Actual field transport

The second namespace, `Langlands.PadicField.AbelianTransport`, uses finite
p-adic fields `F` and `E` with independent carrier universes and a supplied
`e : F.Carrier ≃ₐ[Padic p] E.Carrier`. Here the topologies are the canonical
ones, and the measurable spaces are their Borel spaces.

The published `ConductorTransport.quasicharacter` and `additiveCharacter`
pull the characters back along `e.symm`. The published
`AbelianTransport.haarMeasure` pushes the actual regular Haar measure forward
along `e`. The new `quasicharacter_inv` proves that the first map commutes
with pointwise inversion, by extensionality and reflexivity.

`gammaRegularAt_iff` combines the two published `regularPoint_iff`
comparisons, first rewriting the inverse character by `quasicharacter_inv`.
`gammaRegularPointEquiv` packages the resulting equivalence of subtypes.
Both directions retain the complex coordinate unchanged, and its inverse
laws are definitional. `gammaRegularPointEquiv_val` exposes this fact.

`gammaLRatio_eq` proves equality of the units at corresponding points:
unit extensionality reduces to scalar equality, the polynomial formula
exposes the two evaluations, and the published `lPolynomial_eq` and
`spectralVariable_eq` identify them. The inverse-character equality is
again used for the reflected factor.
Finally `gammaValue_eq` unfolds gamma and substitutes this ratio equality
and the published `epsilon_eq` at the same complex coordinate and transported
Haar measure. This proves compatibility of the direct construction with
these actual transport maps.

## Original source and derived provenance

John Tate, *Number theoretic background* (1979), Corvallis Part II,
section 3.1.3 and section 3.2, especially equation (3.2.1), printed page 13 /
retained PDF page 22, supplies the Euler expression, plus-sign Fourier
kernel, and normalized local functional-equation convention. The original
page was read and checked visually. Equations (3.2.6.1)–(3.2.6.3), printed
pages 13–14 / PDF pages 22–23, give the actual epsilon formulas inherited
through the published `Abelian.Padic` and `Abelian.Laurent` constructions;
these pages were also read in the retained text.

The registered source is `tate-1979-number-theoretic-background`, at
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
with verified SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
No source-specific erratum file was found in the project notes or literature.
The project's separate caution about Tate's scalar self-dual-measure ratio
does not enter this fixed-Haar construction.

To read the convention, replace the character in Tate's (3.2.1) by
`χ |·|^s`. Its reflected character `|·| (χ |·|^s)⁻¹` is
`χ⁻¹ |·|^(1-s)`. Moving the two L denominators gives precisely epsilon
times `L(1-s,χ⁻¹)/L(s,χ)` as the scalar multiplying the unnormalized zeta
integral. This explains the formula's orientation and the unchanged
plus-sign additive character. The module defines that expression; it does
not prove the zeta-integral functional equation.

The common subtype, unit packaging, coefficient reductions, and transport
are derived constructions from the existing project APIs. This module
does not assert maximal analytic continuation, manufacture a self-dual
measure, apply a half shift to the fixed-Haar epsilon, or compare this direct
abelian construction with an explicitly supplied nonabelian system.
It leaves the companion functional equations and nonvanishing theorems
unchanged. The code and exposition are by Worker 20; published dependencies
are imported unchanged.
