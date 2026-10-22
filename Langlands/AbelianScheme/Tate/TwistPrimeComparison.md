# Canonical prime-power maps for roots-of-unity limits

This module constructs the canonical maps from full and prime-to-`m`
roots-of-unity limits to products of their prime-adic twists. It proves
continuity, ring-map naturality and compatibility with restriction.
It does not assert that the comparison maps are isomorphisms.
All declarations are in `Langlands.TateTwist.Divisibility`.

## Provenance

This is an internal construction from the actual groups and power maps in
`Langlands.AbelianScheme.Tate.Twist` and the divisibility limits in
`Langlands.AbelianScheme.Tate.TwistDivisibility`. It introduces no new
torsion group, scalar ring or independently supplied comparison map.
The cited source behind those root constructions is B. Edixhoven,
G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft built
2012-02-08, Chapter X (10.8), printed p.144 (PDF p.148), with the prime and
field convention on printed p.141 (PDF p.145). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
That passage was read in developing the prime-adic construction and its
retained extract was reread for this work. No source-specific errata file
was present in the available Library.

The original passage treats a prime-adic limit over a separable closure.
The arbitrary-ring coordinate-extraction and product APIs here are
derived internally. Their proofs use only the defining compatibility
equations, not any rank, finite-étaleness or decomposition theorem.

## Prime-power extraction

Let `R` be a commutative ring, `P : ℕ → Prop`, and `p` a prime.
Given `hP : ∀ n, P (p ^ n)`, `primePowerIndex P p hP n` is the positive
index `p ^ n` in the divisibility system. Its positivity follows from
primality of `p`.

`toPrime R P p hP` is an additive map from `Integral R P` to the existing
prime-adic twist `Langlands.TateTwist.Integral R p`. It sends a family
`x` to the sequence whose `n`th coordinate is `x` at `p ^ n`. The sequence
is coherent because the full divisibility compatibility equation applies
to `p ^ n ∣ p ^ (n + 1)`. Thus its transitions are the previously
constructed power-by-`p` transitions on actual roots of unity.

`evaluation_toPrime` is the coordinate formula. `continuous_toPrime`
follows from continuity of each source evaluation, followed by the
product and subtype topology. `toPrime_map` proves that extraction
commutes with the maps induced by actual ring homomorphisms.

`fullToPrime R p` specializes to all positive indices.
`awayToPrime R p m h` specializes to those coprime to `m`, where
`h : Nat.Coprime p m`; coprimality of every power follows from `h`.
Both maps are continuous. `awayToPrime_restrictAway` proves that first
restricting a full family to the away system gives the same prime
sequence whenever `p` is retained.

The excluded modulus `m` is any natural number. For prime `m`, the
retained primes are precisely the other primes. The code uses
coprimality throughout and does not silently assume primality of `m`.

## Product maps

`PrimeProduct R` is the product over `p : Nat.Primes` of the existing
prime-adic twists. `AwayPrime m` consists of primes coprime to `m`;
`AwayPrimeProduct R m` is the product over that subtype. These products
inherit additive groups and product topologies. The local prime instance
is obtained from each prime's subtype proof and introduces no additional
hypothesis.

`toPrimeProduct R` and `toAwayPrimeProduct R m` bundle all the corresponding
extraction maps into additive product maps. They are continuous because
each component is continuous. `primeProductRestrict R m` forgets the
prime components not coprime to `m`; it is additive and continuous.
`toPrimeProduct_restrictAway` states that extracting after restriction
agrees with restricting the extracted product.

For a ring homomorphism `f : R →+* S`, `primeProductMap f` and
`awayPrimeProductMap m f` apply the existing prime-adic map at every prime.
They are additive and continuous. Their identity and composition laws
follow coordinatewise from the published prime-adic laws.
`toPrimeProduct_map` and `toAwayPrimeProduct_map` prove naturality of the
canonical comparison maps. `primeProductRestrict_map` expresses
naturality of product restriction. The coordinate identities are
definitional equalities; they do not use an inverse comparison map.

## Scope

These definitions construct continuous additive comparison maps, with
their exact root-coordinate meaning. They do not assert injectivity,
surjectivity, a continuous inverse, a comparison of scalar rings, or a
restricted-product comparison after rationalization. Those are separate
theorem obligations. The elementary maps here require no field,
characteristic or finiteness hypothesis and imply no rank statement.
