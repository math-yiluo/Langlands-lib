# Prime-product decompositions of roots-of-unity Tate twists

This module proves the published proposition
`Langlands.TateTwist.Divisibility.PrimeProductComparisons R` for every
`R : Type u` with `[CommRing R]`. The main theorem is
`Langlands.TateTwist.Divisibility.primeProductComparisons`.
The two component theorems are `fullPrimeProductComparison` and
`awayPrimeProductComparison` in the same namespace.

The full equivalence has underlying additive homomorphism exactly
`toPrimeProduct R`. For every natural modulus `m`, the away equivalence
has underlying additive homomorphism exactly `toAwayPrimeProduct R m`.
Both equivalences and their inverses are continuous for the published
product and subtype topologies.

## Provenance and scope

This is an internal proof of the comparison obligation published in
`Langlands.AbelianScheme.Tate.TwistPrimeComparisonStatement`. It imports
that statement and uses the actual root groups, transition maps, limits,
and continuity results of its existing imports. The arbitrary-ring
comparison is the internal target described in that statement's Markdown;
this proof does not attribute it to the field-based prime-adic convention
in the literature cited there. Its additional Mathlib inputs are elementary
Bézout arithmetic and induction on coprime prime-power factors.

No field, domain, characteristic, primitive-root, root-existence,
finite-root-group, or compactness assumption is added. The argument works
in any universe of commutative rings, including rings with zero divisors.
The modulus is unrestricted, including `0` and `1`.

## Finite-order reconstruction

For coprime positive integers `a` and `b`, the transition maps from order
`a*b` to orders `a` and `b` send an ambient additive unit `z` to `b • z`
and `a • z`, respectively. The private lemma `bezout_reconstruct` starts
with `a • x = 0` and `b • y = 0` in an additive commutative group.
Writing

```text
a * gcdA(a,b) + b * gcdB(a,b) = 1,
z = gcdB(a,b) • x + gcdA(a,b) • y,
```

it proves `(a*b) • z = 0`, `b • z = x`, and `a • z = y`.
Applied to `Additive Rˣ`, this constructs an actual order-`a*b` root
with the prescribed transitions. Thus it includes the exponent corrections
required by the quotient-power transitions. Injectivity follows because
an ambient difference killed by both coprime integers is zero.

The lemma `level_prime_ext` applies `Nat.recOnPrimeCoprime` to show that
a root of any positive order is determined by its transitions to all
dividing prime powers. The prime-power case reads its own coordinate;
the coprime-product case uses the binary injectivity just proved.

The same induction proves `exists_continuous_coordinate`: for every
positive order `n`, there exists a continuous function from the full prime
product to the order-`n` root group whose transition to every dividing
prime power is the specified prime-adic coordinate. At a prime power the
function is coordinate evaluation. Successor coherence of a prime-adic
sequence is extended to all exponent inequalities by induction. A dividing
positive prime power has the same prime; exponent zero is handled by the
trivial order-one root group.

At a coprime product the two previously constructed coordinate functions
are combined by `coprimeJoin`, chosen from binary surjectivity. This join
is continuous since its domain is the product of two discrete root groups.
A positive prime power dividing the product divides one of the coprime
factors, so the prescribed-coordinate property follows from transition
composition. This proves continuity by finite recursion without assuming
that the discrete root groups are finite.

## The full inverse and equivalence

`reconstructedCoordinate` chooses a continuous function from the proved
finite-order existence statement. The resulting family `fromPrimeProduct`
is coherent: both sides of each divisibility transition have the same
prime-power transitions, so `level_prime_ext` identifies them.
Coordinatewise continuity gives continuity into the product, then into
the coherent-family subtype.

Reading the prime-power coordinates of this family recovers the supplied
prime product. Conversely, `level_prime_ext` proves injectivity of the
published forward map. These two facts provide the inverse identities
for `fullPrimeEquiv`, which directly extends `toPrimeProduct R` as an
additive homomorphism. Equality of the underlying homomorphism is therefore
reflexive. Forward continuity is the published theorem; inverse continuity
is the construction above.

## All away moduli

`extendAwayPrimeProduct` extends a family on the retained primes to the
full prime product by assigning zero to excluded components. Each component
is an evaluation or a constant, hence this extension is continuous.
`fromAwayPrimeProduct` composes this extension with the full inverse and
then with the published continuous restriction `restrictAway R m`.
The published compatibility of restriction and comparison proves that this
is a right inverse to `toAwayPrimeProduct R m`.

For injectivity, a positive prime power dividing an allowed order has
prime base coprime to `m`, so its coordinate is available in the away
product. Exponent zero again uses the trivial order-one group. Applying
`level_prime_ext` gives injectivity and the remaining inverse identity.
The additive equivalence directly extends the published away homomorphism.
All these arguments quantify over arbitrary `m`, so no exceptional modulus
is omitted. Finally the two component theorems form the exact conjunction
required by `PrimeProductComparisons R`.
