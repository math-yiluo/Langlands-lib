# Test-scheme restriction on prime-adic Tate modules

Fix a scheme `S`, a commutative group object `G` in `Over S`, a prime natural
number `p`, and an arrow `a : T' ⟶ T` of test schemes over `S`.
This module constructs restriction on the existing actual prime-adic Tate
modules. An abelian scheme is included by taking `G = A.toGrp`.

## Provenance

This is an internal consequence of `TestScheme`, `PrimeAdic` and
`PrimeComparison`. The finite-level map is precomposition on the actual
sections of the kernel of multiplication by `p ^ n`. The imported
`levelRestrict_transition` supplies compatibility with the actual torsion
transition maps. No new original-literature assertion is used.

## Integral construction

`levelTestRestrict` is the existing `levelRestrict` at order `p ^ n`, bundled
as a linear map over `ℤ_[p]`. Its scalar law follows from `ZMod.map_smul`:
the scalar acts through its image under `PadicInt.toZModPow n` at this level.

`testRestrict` lifts these maps to the published carrier
`PrimeAdic.Integral G T p`, the coherent sequences of actual prime-power
torsion sections. Its coordinate formula is

```
evaluation G T' p n (testRestrict G p a x)
  = levelRestrict G a (p ^ n) (evaluation G T p n x).
```

The transition equation follows from `levelRestrict_transition` and the
coherence of `x`. The identity and contravariant composition laws are proved
coordinatewise by identity and associativity of composition in `Over S`:
restriction along `b ≫ a`, with `b : T'' ⟶ T'`, is restriction along `a`
followed by restriction along `b`.

The map is continuous for the existing product-subspace topologies.
Each coordinate is a continuous evaluation followed by a map out of a
discrete torsion level. `continuousTestRestrict` bundles this continuity and
the same `ℤ_[p]`-linear function. This argument requires no finiteness claim.

## Rational construction and naturality

`rationalTestRestrict` extends `testRestrict` from `ℤ_[p]` to `ℚ_[p]` on
`PrimeAdic.Rational G T p = ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral G T p`.
It sends `q ⊗ x` to `q ⊗ testRestrict G p a x` and satisfies the identity
and contravariant composition laws by functoriality of scalar extension.

For an actual group-object homomorphism `f : G ⟶ H`, restriction commutes
with the induced prime-adic map:

```
testRestrict H p a (map T p f x)
  = map T' p f (testRestrict G p a x).
```

The integral proof is associativity of precomposition and postcomposition
on sections. The rational proof expresses this identity as equality of
composed linear maps, applies scalar extension, and evaluates the resulting
identity. Thus it concerns the existing actual `rationalMap`.

## Coordinate extraction and abelian schemes

In namespace `PrimeComparison`, `toPrime_testRestrict` says that extraction
of the `p ^ n` coordinates commutes with restriction whenever the chosen
predicate `P` contains all these orders. `fullToPrime_testRestrict` gives the
full specialization. `awayToPrime_testRestrict` retains the explicit
hypothesis `Nat.Coprime p m` for extracting prime-power coordinates from
the system of orders coprime to the natural modulus `m`. All three
identities hold by the coordinate definitions.

The two abbreviations in `AbelianScheme.Tate.PrimeAdic` specialize the
continuous integral map and algebraic rational map to the actual group
object of an abelian scheme.

## Scope

The base `S` is fixed. This module changes the test scheme within `Over S`;
it does not construct change of the base scheme or transport along a path
between geometric fibre functors. The rational map is algebraic: no rational
topology or continuity is asserted. No rank, finite étaleness, monodromy,
Weil pairing or completion of the parent PEL construction is asserted.
