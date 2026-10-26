# Domain stalks of smooth schemes over fields

`Langlands.AlgebraicGeometry.SmoothDomainStalks.{u}` is the following
`Prop`-valued definition:

```lean
∀ (K : Type u) [Field K] (X : Scheme.{u})
  (p : X ⟶ Spec (CommRingCat.of K)),
  Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x)
```

Here `Scheme`, `Smooth`, `Spec`, and `IsDomain` are Mathlib's existing notions.
`X.presheaf.stalk x` is the commutative local ring of the structure sheaf at
the point `x`; its coercion to a ring is the argument of `IsDomain`. That
predicate includes nontriviality and absence of zero divisors. The single
universe parameter `u` is arbitrary.

The field and the smooth scheme are arbitrary. No quasi-compactness,
perfectness, algebraic closedness, characteristic, separation, group structure,
connectedness, reducedness, regularity, normality, or prior integrality
hypothesis is imposed. The empty scheme satisfies the stalk conclusion
vacuously.

## Original sources and derived provenance

This statement is a consequence of the following original Stacks Project
results and definitions.

1. [Tag 056T](https://stacks.math.columbia.edu/tag/056T), Lemma 33.25.4,
   states geometric regularity, geometric normality, and geometric reducedness
   for schemes smooth over a field. Its proof establishes ordinary normality
   using regularity. The retained file is `056T.html` in literature source
   `stacks-global-functions-field-and-fibre-criterion-2026-10-23`, content SHA256
   `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`.
2. The regularity route in that proof is
   [Tag 056S](https://stacks.math.columbia.edu/tag/056S), Lemma 33.25.3,
   followed by [Tag 0569](https://stacks.math.columbia.edu/tag/0569),
   Lemma 28.9.4. These give regularity for a scheme smooth over a field and
   normality for a regular scheme, respectively. The retained files
   `056S.html` and `0569.html` belong to
   `stacks-smooth-connected-integral-2026-10-24`, content SHA256
   `5374d7e59f547f5114ea9217b3fdfc3c6d0b3f9cf7ab3ed0f35da7163ba7f794`.
3. [Tag 033I](https://stacks.math.columbia.edu/tag/033I), Definition 28.7.1,
   defines a normal scheme by requiring every local ring to be a normal
   domain. [Tag 0309](https://stacks.math.columbia.edu/tag/0309),
   Definition 10.37.1, defines a normal domain as a domain integrally closed
   in its fraction field. The retained files `033I.html` and `0309.html`
   belong to `stacks-normal-scheme-domain-stalk-definitions-2026-10-25`,
   content SHA256
   `4b962e26e7516ff782a6f7b146df1c0c9972c10ecdbf685912db247b39209e79`.

For the given smooth structure morphism `p`, the first two sources give
normality of `X`. The third identifies each local ring as a domain, which
is exactly the stalk conclusion above. The original tagged statements,
proofs, and definitions were read directly; no project errata file was
present for these three source collections when this statement was prepared.

## Proof boundary

The Lean file defines this proposition and supplies no proof. The regularity
and normality implications describe its provenance; no new scheme regularity
or normality class is introduced. A separate proof must establish this exact
published proposition.
