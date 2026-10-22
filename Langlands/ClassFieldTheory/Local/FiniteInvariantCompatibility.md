# The invariant diagram on ordinary relative classes

Author: Worker 42.

This module imports the published `InvariantCompatibility` and
`FiniteComparison`. It defines the ordinary relative-class presentation of
the invariant diagram and proves that this presentation is equivalent to the
existing continuous finite-stage presentation.

## Ordinary compatibility predicate

`InvariantFamily.OrdinaryClosureCompatibility I` is a proposition on a raw
invariant family `I`. For every prime `p`, every `p`-adic field `F`, every finite
Galois intermediate field `E` of its algebraic closure, and every ordinary
relative class `x` in degree two, the required equation is

```
I.absolute F (closureInflation F.Carrier E 2 x) = I.relative F E x.
```

Both sides lie in the actual additive quotient `Q/Z` used by `InvariantFamily`.
The map `closureInflation` is the constructed inverse of the finite
continuous-to-ordinary comparison followed by continuous inflation. It uses
restriction of actual automorphisms and inclusion of actual units. This
diagram keeps the base field fixed: it restricts the absolute invariant to
relative classes, with no degree multiplier.

The base field and its algebraic-closure intermediate fields inhabit one
arbitrary common universe. Thus the predicate applies to all primes and
all finite extensions of `Q_p`, without a `Type 0` restriction.

## Equivalence certificate

`InvariantFamily.closureCompatibility_iff` proves that the existing
compatibility predicate, tested on continuous finite-stage classes,
is equivalent to `OrdinaryClosureCompatibility`. The forward implication
represents an ordinary class by the inverse comparison and cancels the forward
comparison with its inverse. The reverse implication applies ordinary
compatibility to the forward comparison of a continuous class and rewrites
using `closureInflation_continuousToRelative`.
This is an equivalence of predicates on the same raw invariant family.
It does not assert that either predicate holds. This module does not
construct an invariant family or assert existence, normalization, injectivity
of inflation, restriction multiplication by degree, or corestriction laws.
Its equivalence certificate uses no local-field existence theorem or
supplied inverse.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, 1979, Chapter XIII, section 3,
Propositions 6–7 and Corollary 2, printed pp.193–194 / PDF pp.198–199,
supplies the invariant framework. In particular, Corollary 2 describes the
restriction of the absolute invariant to relative degree-two classes.
`OrdinaryClosureCompatibility` records the equality part of that description
for the two maps of an arbitrary family. It does not claim Corollary 2's
injectivity or image theorem. Chapter X, section 3, printed p.154 / PDF p.160,
supplies the finite-stage continuous-cohomology setting used by the imported
comparison and inflation maps.

The predicate presentation and its equivalence certificate are derived
implementation content: the proof is inverse-equivalence cancellation, not a
new proof of Serre's invariant theorem. Both presentations use the same
invariant maps, so the conversion does not change the invariant sign or the
arithmetic/geometric reciprocity convention.

Registered source: `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
