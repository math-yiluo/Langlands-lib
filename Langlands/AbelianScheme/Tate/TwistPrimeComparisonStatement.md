# Prime-product comparison obligations for actual Tate twists

This module states the full and away prime-product comparison obligations
for the actual roots-of-unity limits. It defines propositions only.
No comparison equivalence or proof of these propositions is supplied here.
All three declarations are in `Langlands.TateTwist.Divisibility`.

## Provenance

These are derived comparison targets for the constructions in
`Langlands.AbelianScheme.Tate.TwistDivisibility` and
`Langlands.AbelianScheme.Tate.TwistPrimeComparison`. Those modules define
the actual root limits, product topologies and coordinate-extraction maps.
The underlying prime-adic twist is the one described in B. Edixhoven,
G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft built
2012-02-08, Chapter X (10.8), printed p.144 (PDF p.148); the chapter's field
and prime convention is on printed p.141 (PDF p.145). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The original passage was read for the imported twist construction and
its retained extract was reread while preparing this statement.

That passage treats the prime-adic twist over a separable closure.
It does not assert the arbitrary-ring full or away comparison stated
here. These targets arise internally from decomposing a positive torsion
order into its coprime prime powers and comparing the corresponding
compatible families of roots. Establishing this decomposition and its
topological consequences is the separate proof obligation. Neither
enough roots of unity nor a chosen primitive root is an input.

## Exact propositions

For any commutative ring `R`, `FullPrimeProductComparison R` asserts that
there exists an additive equivalence

```text
e : Full R ≃+ PrimeProduct R
```

such that `e.toAddMonoidHom = toPrimeProduct R`, and both `e` and `e.symm`
are continuous. Here `Full R` consists of families of actual roots
indexed by all positive integers, compatible with the quotient-power
transition for every divisibility relation. `PrimeProduct R` is the
product of the actual prime-adic twists over all `p : Nat.Primes`.
The specified forward map reads the `p^n` coordinate at every prime `p`
and exponent `n`.

For any natural number `m`, `AwayPrimeProductComparison R m` asserts that
there exists an additive equivalence

```text
e : Away R m ≃+ AwayPrimeProduct R m
```

such that `e.toAddMonoidHom = toAwayPrimeProduct R m`, and both directions
are continuous. The source retains positive indices `N` with
`Nat.Coprime N m`; the target retains primes `p` with `Nat.Coprime p m`.
The forward map again reads the actual prime-power coordinates.
The parameter `m` is unrestricted. In particular, `m = 1` retains every
positive index and every prime, while `m = 0` retains only the index `1`
and no prime.

`PrimeProductComparisons R` is the conjunction

```text
FullPrimeProductComparison R ∧ ∀ m : ℕ, AwayPrimeProductComparison R m.
```

It is the combined target of the separate decomposition proof task.
The two component propositions remain individually available to consumers.

## Topology and scope

Each finite-order root group in the imported construction is given the
discrete topology. A coherent root limit has the subtype topology from
the product of those groups, and the prime products have the product
topology of the prime-adic limits. These are the exact topologies in the
continuity clauses. No finiteness, compactness, field or characteristic
assumption is imposed.

Requiring equality with the already defined additive map fixes the
comparison on every coordinate. An arbitrary abstract equivalence
between the source and target would not satisfy the statement without
this equality. Forward continuity is already proved in the imported
module; bijectivity and continuity of the inverse remain to be proved.

The statements concern additive groups and their topologies. They do
not assert a scalar-ring comparison, linearity over a product of local
scalar rings, a rank or freeness theorem, a rational restricted-product
comparison, or an equivariant trivialization of any twist. The imported
maps already satisfy ring-map naturality and compatibility with away
restriction; this module does not add new naturality assertions.
