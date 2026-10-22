# Products of completed integers and integral finite adeles

This internal construction provides the place and completion identifications
needed in the normalized rational profinite-integer comparison. It introduces
no alternative adele ring and assumes no comparison with a residue inverse limit.

## Product of the actual local integer rings

For every number field `K`, `integralFiniteAdelesProductEquiv K` is the ring
equivalence

```lean
(∀ v : FinitePlace K, v.adicCompletionIntegers K) ≃+* integralFiniteAdeles K
```

Here `FinitePlace K` is the published abbreviation for
`HeightOneSpectrum (NumberField.RingOfIntegers K)`. Its factors are the actual
adic completion integer subrings. The target is the existing subring of finite
adeles integral at every place, with the topology inherited from the restricted
product. The source has the product of the local subspace topologies.

The forward map is `RestrictedProduct.structureMap` with the everywhere-integral
membership proof. The inverse takes the coordinates and their integrality
proofs. Both inverse laws and the ring laws are definitional. The theorem
`integralFiniteAdelesProductEquiv_apply` records its coordinate formula.

`continuous_integralFiniteAdelesProductEquiv` uses
`RestrictedProduct.isEmbedding_structureMap.continuous` and the induced target
topology. The inverse-continuity theorem uses continuous restricted-product
coordinate evaluation, followed by the induced local integer-ring topology and
the product topology. Thus this is a topological ring identification with the
actual integral subring, not just a bijection between families.

## Rational prime indexing

`rationalPadicProductIntegralEquiv` is the explicit ring equivalence

```lean
(∀ p : Nat.Primes, PadicInt p.val) ≃+* integralFiniteAdeles ℚ
```

Its definition reindexes by `Rat.HeightOneSpectrum.primesEquiv`, then uses the
inverse of `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv` in each
coordinate, and finally applies the preceding product equivalence. Primality
instances are local consequences of membership in `Nat.Primes`.

The theorem `rationalPadicProductIntegralEquiv_apply` states that the coordinate
at the actual place `v` is

```lean
(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
  (x (Rat.HeightOneSpectrum.primesEquiv v))
```

where the p-adic integer is coerced into the p-adic field. This equality is
by reflexivity: Mathlib's integral and field comparisons have compatible
underlying maps. It makes the place and completion identifications explicit.

Continuity of the forward map follows from continuous local equivalences and
coordinate reindexing. Continuity of the inverse follows from the inverse
product equivalence, the forward local equivalences and
`Homeomorph.piCongrLeft`. These proofs use the actual topologies in both
directions and need no compact-to-Hausdorff shortcut.

`rationalPadicProductIntegralEquiv_intCast` proves that the family of p-adic
images of any `z : ℤ` maps, in the ambient finite adele ring, to
`algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ)`. It follows from preservation of integer
casts by ring maps and the inclusion of the integral subring.

## Provenance and boundaries

The construction is an internal composition of the published
[`IntegralFiniteAdeles`](IntegralFiniteAdeles.md) construction with pinned
Mathlib's explicit equivalences in
`Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean`, and the product-topology
interface in `Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`.
The project Mathlib pin is `5ed2965256430c3649e86755f9576b54eca72435`.
No claim here is attributed verbatim to an original literature theorem.

This module does not identify `ProfiniteIntegerRing` with the p-adic product,
prove rational tensor localization, or address the prime-to-p variant. Those
are separate obligations; this module supplies the explicit actual-place
construction for assembling the full comparison.
