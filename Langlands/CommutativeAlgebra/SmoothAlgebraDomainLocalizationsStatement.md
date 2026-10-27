# Domain prime localizations of smooth algebras over fields

`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations.{u, v}` is the
following `Prop`-valued definition:

```lean
∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A],
  Algebra.Smooth K A →
    ∀ (p : Ideal A) [p.IsPrime], IsDomain (Localization.AtPrime p)
```

It says that if `A` is a smooth algebra over a field `K`, then the
localization `A_p` of `A` at every prime ideal `p` is a domain.

`Field`, `CommRing`, `Algebra`, `Algebra.Smooth`, `Ideal.IsPrime`,
`Localization.AtPrime`, and `IsDomain` are Mathlib's existing notions; the
module imports only Mathlib. `Algebra.Smooth K A` means that `A` is formally
smooth and of finite presentation over `K`. Mathlib's `stacks` attribute on this
class cites Stacks Tag 00T2. It notes that the Stacks Project defines smooth ring
maps differently and that Stacks Tag 00TN proves the two definitions equivalent.
`Localization.AtPrime p` is the localization of `A` at the complement of `p`.
`IsDomain` includes nontriviality as well as the absence of zero divisors.

The universe parameters `u` of the field and `v` of the algebra are arbitrary
and independent. The field is arbitrary, and `A` is any smooth `K`-algebra. No
perfectness, characteristic, algebraic closedness, connectedness, reducedness,
normality, regularity, or prior domain hypothesis is imposed. In particular, `A`
itself need not be a domain or connected; the conclusion concerns each prime
localization separately. If `A` is the zero ring, it has no prime ideals and the
conclusion holds vacuously.

## Original sources and derived provenance

This is a ring-level restatement derived from the following original Stacks
Project results and definitions. All of them except Tag 0309 are stated for
schemes. The proposition is not a verbatim translation of any one of them.

1. [Tag 056T](https://stacks.math.columbia.edu/tag/056T), Lemma 33.25.4,
   states that a scheme smooth over a field is geometrically regular,
   geometrically normal, and geometrically reduced. Its proof shows that such a
   scheme is regular and normal. The retained file is `056T.html` in literature
   source `stacks-global-functions-field-and-fibre-criterion-2026-10-23`,
   content SHA256
   `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`.
2. That proof uses [Tag 056S](https://stacks.math.columbia.edu/tag/056S),
   Lemma 33.25.3, which says a scheme smooth over a field is regular, and
   [Tag 0569](https://stacks.math.columbia.edu/tag/0569), Lemma 28.9.4, which
   says a regular scheme is normal. The retained files `056S.html` and
   `0569.html` belong to `stacks-smooth-connected-integral-2026-10-24`, content
   SHA256 `5374d7e59f547f5114ea9217b3fdfc3c6d0b3f9cf7ab3ed0f35da7163ba7f794`.
   The proof of 056S takes the regularity of each local ring from Algebra,
   Lemma 10.140.3. That lemma is not among the registered sources and is named
   here only to show where the ring-level step occurs.
3. [Tag 033I](https://stacks.math.columbia.edu/tag/033I), Definition 28.7.1,
   defines a scheme to be normal if every local ring is a normal domain.
   [Tag 0309](https://stacks.math.columbia.edu/tag/0309), Definition 10.37.1,
   defines a normal domain as a domain integrally closed in its fraction field.
   The retained files `033I.html` and `0309.html` belong to
   `stacks-normal-scheme-domain-stalk-definitions-2026-10-25`, content SHA256
   `4b962e26e7516ff782a6f7b146df1c0c9972c10ecdbf685912db247b39209e79`.

The derivation applies these sources to the affine scheme `X = Spec A` with its
structure morphism to `Spec K`.

- Since `A` is a smooth `K`-algebra, the morphism `X → Spec K` is smooth. In
  Mathlib, when `K` and `A` lie in one universe,
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff` for
  `AlgebraicGeometry.Smooth`, together with `RingHom.smooth_algebraMap`,
  identifies smoothness of `Spec.map` of the algebra map with
  `Algebra.Smooth K A`.
- By items 1 and 2, `X` is normal. By item 3, every local ring of `X` is a
  normal domain, and in particular a domain.
- The points of `X` are the prime ideals `p` of `A`, and the local ring of `X`
  at `p` is the localization `A_p`. In Mathlib,
  `AlgebraicGeometry.StructureSheaf.stalkIso` is an `A`-algebra isomorphism from
  `Localization.AtPrime p` to the stalk of the structure sheaf of `Spec A` at
  `p`.

Hence `A_p` is a domain for every prime `p`, which is the conclusion above.

The Stacks Project does not track universes. In Mathlib, a scheme morphism
`Spec A ⟶ Spec K` requires `K` and `A` to lie in one universe, whereas here
they may lie in different universes. Consequently this proposition is not literally the affine case of the
published `Langlands.AlgebraicGeometry.SmoothDomainStalks.{u}`, which uses one
universe. The size of the types imposes no additional mathematical hypothesis.

The original tagged statements, proofs, and definitions were read directly.
The Stacks Project has no separate errata file. On 27 October 2026 the current
official pages for all five tags were byte-identical to the retained files. Their
comments, and those on Sections 28.7 and 10.37 which contain 033I and 0309,
make no correction affecting these items. This check is registered as
`stacks-smooth-domain-localizations-current-check-2026-10-27`.

## Relation to the scheme-level statement

This module does not import or use
`Langlands.AlgebraicGeometry.SmoothDomainStalks` or any pointed-morphism
rigidity target. It is intended as the ring-level input to a proof of that scheme-level
proposition. A smooth scheme over a field has affine charts whose section rings
are smooth algebras over the field, and each stalk is a prime localization of
such a ring. That scheme adapter is not part of this pair.

## Proof boundary

The Lean file defines this proposition and supplies no proof. The regularity
and normality steps above describe its provenance; no new regularity or
normality notion is introduced. A separate proof must establish this exact
proposition.
