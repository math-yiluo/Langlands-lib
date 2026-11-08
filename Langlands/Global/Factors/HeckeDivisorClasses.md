# Principal generators and ideal-class representatives of finite Hecke divisors

Worker 1692 builds this internal arithmetic decomposition for the global Hecke
unfolding requested by Worker 1798. It uses the Library's existing finite
divisor `FinitePlaceDivisor K`, its prime-product fractional ideal
`finiteDivisorFractionalIdeal`, the principal divisor of `HeckeDivisor`, and
Mathlib's actual class group `ClassGroup (𝓞 K)`. The number field has
unrestricted universe `u`. Mathlib's `ClassNumber` instance makes this class
group a `Fintype`; it is imported here so that index type is available.

## Principal divisors and generators

`principalDivisor_inv` follows from multiplicativity. Global integral units
have zero principal divisor, and their map into `Kˣ` is injective because
`𝓞 K → K` is injective.

`principalDivisors K` is the additive subgroup of finite divisors whose carrier
is exactly the range of `principalDivisor`. `principalGenerator p` is a chosen
element of `Kˣ` whose principal divisor is `p`.

`principalUnitsEquiv : principalDivisors K × (𝓞 K)ˣ ≃ Kˣ` sends `(p, u)` to
`u * principalGenerator p`, with `u` included by `Units.map`. It is injective
because applying `principalDivisor` recovers `p`; then cancelling the common
generator and integral-unit injectivity recover `u`. It is surjective because,
for `a`, the quotient of `a` by the generator of its divisor has zero divisor.
The existing kernel theorem `principalDivisor_eq_zero_iff` makes that quotient
an integral unit. The first coordinate of the inverse is `principalDivisor a`.

## Divisor classes

`divisorClass d` is `ClassGroup.mk K` of the prime-product fractional ideal of
`d`. The existing multiplicativity of that fractional ideal gives the zero,
addition, negation and subtraction laws. Every class is a divisor class:
Mathlib's class-group induction gives a nonzero fractional ideal `I`, and the
existing inverse divisor `fractionalIdealDivisor K I` maps back to `I`.

`divisorClass_eq_one_iff` identifies the kernel with `principalDivisors K`.
Mathlib's `ClassGroup.equiv K` and `ClassGroup.equiv_mk` reduce triviality to
membership in the range of `toPrincipalIdeal (𝓞 K) K`. A generator `a` turns
this into `principalDivisor a = d` by the existing principal fractional-ideal
comparison and injectivity of prime multiplicities. The converse uses the same
comparison. Consequently, two divisors have equal classes exactly when their
difference is principal.

`classRepresentative C` is a chosen divisor with class `C`. There are two
actual bijections:

- `classPrincipalEquiv : ClassGroup (𝓞 K) × principalDivisors K ≃ FinitePlaceDivisor K`
  with `(C, p) ↦ p + classRepresentative C`;
- `classPrincipalNegEquiv : ClassGroup (𝓞 K) × principalDivisors K ≃ FinitePlaceDivisor K`
  with `(C, p) ↦ p - classRepresentative C`.

For the first map, taking classes recovers `C` because principal divisors have
trivial class; cancelling the representative recovers `p`. Its inverse sends
`d` to its class and `d - classRepresentative (divisorClass d)`. For the second
map, taking classes recovers `C⁻¹`. Its inverse sends `d` to
`(divisorClass d)⁻¹` and `d + classRepresentative (divisorClass d)⁻¹`.

These results do not establish theta-coefficient identities, Poisson
summation, unit-cone integrals, analytic continuation or the global functional
equation.
