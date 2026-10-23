# Prime-product comparisons for actual Tate limits

This module proves exactly the published proposition
`Langlands.GroupScheme.Tate.PrimeComparison.PrimeProductComparisons G T`.
Its main theorem is
`Langlands.GroupScheme.Tate.PrimeComparison.primeProductComparisons`.
The component theorems are `fullPrimeProductComparison` and
`awayPrimeProductComparison` in the same namespace.

The parameters remain an arbitrary scheme `S : Scheme.{u}`, a group object
`G : Grp (Over S)` with `[IsCommMonObj G.X]`, and a test scheme `T : Over S`.
The full additive equivalence has underlying homomorphism exactly
`toPrimeProduct G T`; for every `m : ℕ`, the away equivalence has underlying
homomorphism exactly `toAwayPrimeProduct G T m`. Both equivalences and their
inverses are continuous for the existing product and subtype topologies.

## Provenance and actual carriers

This is an internal proof of the derived obligation in
`Langlands.AbelianScheme.Tate.PrimeComparisonStatement`. It imports that
unchanged statement and uses its actual torsion-section groups and limits.
The statement's Markdown explains the relation of these conventions to
Harris–Taylor, Chapter I, printed p.18; the arbitrary group-scheme comparison
is derived infrastructure, not a theorem attributed to that page.

Worker 18 adapted the proof pattern of Worker 18's published
`TwistPrimeComparisonProof`. Its coprime induction and inverse-continuity
argument are reused, but the finite-level reconstruction here takes place
in `Additive (T ⟶ G.X)`, the actual group of sections. It does not identify
these sections with roots of unity or replace the published Tate data.
Additional Mathlib inputs provide Bézout coefficients, induction on coprime
prime-power factors, and prime-power divisibility facts.

The imported `levelGroup G T n` is the kernel subgroup of the actual
multiplication morphism on sections. `mem_levelGroup` identifies its
membership condition with `x ^ n = 1`. The carrier `Level G T n` is its
additive notation, with discrete topology, and `toSection` is its injective
homomorphism to the ambient additive section group. Divisibility transitions
from order `b` to order `a` are multiplication by `b / a`.
The existing `kernelLevelEquiv` connects these groups to points of the
actual multiplication kernels; this proof needs no new comparison of
carriers.

No finite-level finiteness, rank, characteristic, finite-étaleness,
compactness, or comparison assumption is added. The result also applies to
the published actual abelian-scheme specializations by taking `G = A.toGrp`.
It asserts no rational restricted-product, residue-ring, scalar-ring,
Weil-pairing, or monodromy comparison.

## Finite-order reconstruction

For coprime positive integers `a` and `b`, the private lemma
`bezout_reconstruct` works in an arbitrary additive commutative group.
Given `a • x = 0` and `b • y = 0`, the Bézout identity

```text
a * gcdA(a,b) + b * gcdB(a,b) = 1
```

shows that `z = gcdB(a,b) • x + gcdA(a,b) • y` satisfies
`(a*b) • z = 0`, `b • z = x`, and `a • z = y`.
Applied to the underlying actual sections, this yields a point of
`Level G T (a*b)` via `mem_levelGroup`. Its transitions to orders `a` and
`b` recover the supplied points. The coefficients account for the
multiplication-by-quotient transitions. Injectivity of these two transitions
together follows because their ambient difference is killed by both
coprime integers and hence is zero.

`level_prime_ext` uses `Nat.recOnPrimeCoprime`: an order-`n` point for positive
`n` is determined by its transitions to all dividing prime powers. The
prime-power case reads the point itself, and the coprime-product case uses
the binary injectivity above. The order-one group is trivial because its
points are annihilated by one.

The same induction proves `exists_continuous_coordinate`: for each positive
`n` there exists a continuous function from `PrimeProduct G T` to
`Level G T n` whose transition to any dividing `p^k` is the supplied
prime-adic coordinate. At prime powers it is evaluation; successive
coherence of the actual prime-adic limit extends to all exponent
inequalities by induction. A positive prime power dividing a prime power
has the same prime base; exponent zero uses the trivial order-one group.

At a coprime product, the two inductively constructed coordinates are
joined by a chosen finite-level inverse `coprimeJoin`. It is continuous
because its domain is a product of two discrete level groups. Every
positive prime power dividing a coprime product divides one factor, so
transition composition proves the coordinate specification. The argument
uses finitely many discrete coordinates without asserting they are finite
sets.

## Full comparison

`reconstructedCoordinate` chooses each continuous finite-order function.
Their family `fromPrimeProduct` is coherent: both sides of each required
divisibility transition have the same prime-power transitions, so
`level_prime_ext` proves equality. Coordinate continuity gives continuity
into the full compatible-family subtype.

Reading prime-power coordinates of `fromPrimeProduct` recovers the input
prime product. Conversely, equality under the published `toPrimeProduct`
implies equality at all finite orders by `level_prime_ext`, proving
injectivity. These properties supply the two inverse identities.
`fullPrimeEquiv` extends the existing additive homomorphism itself; equality
of its underlying homomorphism with `toPrimeProduct G T` is reflexive.
The published forward-continuity theorem and the inverse-continuity proof
then establish `fullPrimeProductComparison`.

## Every away modulus

`extendAwayPrimeProduct` extends a product indexed by primes coprime to `m`
to all primes, assigning zero to the excluded components. Each component
is an evaluation or a constant, so this extension is continuous.
`fromAwayPrimeProduct` composes it with the full inverse and the existing
continuous restriction `restrictAway G T m`. The published compatibility
of restriction with comparison establishes the right-inverse identity.

For injectivity, a positive prime power dividing an order coprime to `m`
has prime base coprime to `m`. Its coordinate is therefore available in the
away product. Exponent zero uses the order-one group, and `level_prime_ext`
again gives equality of every finite-order coordinate. The resulting
`awayPrimeEquiv` directly extends `toAwayPrimeProduct G T m`; forward and
inverse continuity prove `awayPrimeProductComparison` for arbitrary `m`.

No modulus is excluded: `m = 1` retains all primes, while `m = 0` retains
none and the source has only order-one coordinates. The generic proofs
cover both cases. Finally `primeProductComparisons` pairs the full theorem
with the theorem quantified over all natural away moduli, exactly as in
the unchanged target.
