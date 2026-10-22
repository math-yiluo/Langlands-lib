# Cup product with relative degree-two Galois classes

Author: Worker 42.

## Actual cup maps

For fields `K` and `L` in independent arbitrary universes, an algebra structure
and a finite-dimensional extension, `relativeTateCup K L n c` specializes the
constructed `Langlands.Tate.integralH2Cup` to `unitsRepresentation K L`.
For each relative degree-two class `c`, it is linear over
`IntegerScalars = ULift ℤ`. The family has type

```
H²(Gal(L/K), Additive Lˣ) →
  Ĥⁿ(Gal(L/K), ULift ℤ) → Ĥⁿ⁺²(Gal(L/K), Additive Lˣ).
```

The second coefficient module is the trivial integral representation. Both
Tate groups are Mathlib's cohomology of its connected complex, and the first
argument is ordinary relative degree-two cohomology. The generic map
transports that argument through the proved positive-degree comparison with
Tate cohomology, uses the cup product for scalar multiplication, and reindexes
degree `2 + n` as `n + 2`. The relative degree-two class is on the left.
The field action, unit group and cohomology groups are unchanged. An enumeration
of the finite automorphism group is obtained by `Fintype.ofFinite`.
The construction itself does not require the extension to be Galois.
`relativeTateCup_eq` certifies this specialization by definitional equality.

With the additional Galois hypothesis, `negativeTwoCupToNormQuotient K L c`
postcomposes the degree-minus-two cup map with the published additive
equivalence `tateZeroEquivNormQuotient`. Its target is the existing quotient
`Kˣ / normSubgroup K L`, in additive notation. Its domain is still actual
degree-minus-two integral Tate cohomology; an identification with the
abelianization of `Gal(L/K)` is separate work.

`negativeTwoCupToNormQuotient_bijective_iff` proves that this postcomposition
is bijective exactly when the original cup map is bijective. The proof uses
the bijectivity of the target comparison equivalence. It makes no assertion
that either cup map is bijective and constructs no inverse.

## Predicates on invariant maps

`FundamentalClassTateIsomorphisms K L inv` asserts that for every class `c`
whose invariant is the positive rational class `1 / [L:K]`, and every
integer `n`, `relativeTateCup K L n c` is bijective.
The class is quantified, not chosen, and no invariant isomorphism is an input
to the cup construction.

`InvariantFamily.TateIsomorphisms I` applies this predicate to `I.relative`
for every finite Galois extension of every `p`-adic field. The base fields and
extension fields have independent arbitrary universes; the prime is arbitrary.
This is a predicate on raw invariant data. By itself it neither asserts
existence of such data nor existence of a fundamental class, so it may hold
vacuously for unsuitable invariant maps. A local realization statement must
conjoin it with the existence and normalization laws on the same family.
The simultaneous realization target remains separate.

## Original source and scope

Jean-Pierre Serre, *Local Fields* (1979), Chapter XI, section 3, printed
p.168 / PDF p.174, defines the fundamental class by invariant `1 / [L:K]`
and states in Theorem 1 that its left cup product is bijective in every integer
degree. The predicate above records the bijectivity conclusion for the
constructed maps. Serre's class-formation assumptions belong to the theorem
that establishes this predicate; this module does not prove that theorem.

The special case on printed p.169 / PDF p.175 identifies the target in degree
zero with the norm quotient. It also identifies the source in degree minus
two with the Galois abelianization, a further comparison not supplied here.
Serre calls the inverse of the resulting map the reciprocity isomorphism.
We retain the arithmetic convention, the positive fundamental invariant and
the fundamental class on the left. The host's geometric reciprocity convention
inverts the arithmetic output. No reciprocity map is constructed in this pair.

The source's restriction, corestriction and inflation formulas on p.169 are
separate compatibility obligations; no such law is asserted here. The local
specialization and the postcomposition bijectivity certificate are derived
implementation content, using the generic Tate cup construction and the
published field norm-quotient comparison.

Registered original: `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 42 read the cited original pages directly.
