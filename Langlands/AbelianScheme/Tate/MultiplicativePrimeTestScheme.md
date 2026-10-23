# Test-scheme naturality of the prime-adic multiplicative comparison

Fix a scheme `S`, a prime natural number `p` and an arrow `a : T' ⟶ T`
in `Over S`. The induced map of global-section rings is
`a.left.appTop.hom : Γ(T.left, ⊤) →+* Γ(T'.left, ⊤)`.

## Provenance and integral square

This internal unit combines the actual restriction maps of `PrimeTestScheme`
with the published `primeIntegralEquiv`, `primeRationalEquiv` and the
finite-level law `levelEquiv_restrict`. No new original-literature assertion
is used. The comparison targets the actual coherent families of roots of
unity in the global-section ring; it chooses no roots or trivialization.

`primeIntegralEquiv_testRestrict` proves

```
primeIntegralEquiv T' p (Tate.PrimeAdic.testRestrict (Gm S).toGrp p a x)
  = TateTwist.map p a.left.appTop.hom (primeIntegralEquiv T p x).
```

This is a square between the actual `Gm` Tate modules and the existing
roots-of-unity limits. The proof applies `levelEquiv_restrict` at each
prime-power order. `primeIntegralEquiv_symm_testRestrict` proves the
inverse comparison square by applying the injective target comparison and
its inverse identities. The integral restriction and comparisons retain
the continuity already proved for their inverse-limit topologies.

## Rational square

`primeRationalEquiv_testRestrict` gives the same square after scalar extension
from `ℤ_[p]` to `ℚ_[p]`:

```
primeRationalEquiv T' p
    (Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p a x)
  = TateTwist.rationalMap p a.left.appTop.hom (primeRationalEquiv T p x).
```

Its proof expresses the integral square as equality of composed linear
maps, applies scalar extension, and evaluates the result.
`primeRationalEquiv_symm_testRestrict` proves the inverse square using
injectivity, as for the integral case.

These laws vary test schemes over a fixed base. They do not assert change
of base `S`, geometric path transport, monodromy compatibility, rational
topology, finite rank, a Weil pairing or completion of the parent PEL task.
