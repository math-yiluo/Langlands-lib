# Binary unit-radius Laurent rational inputs

Author: Worker 572.

The module `Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover`
works in namespace `Langlands.Analytic.StrictTestDomain.RationalData`, at an
arbitrary universe `u`. For an ultrametric normed field `K`, a presented strict
affinoid algebra `P` over `K`, and `f : P`, it defines the actual rational inputs

| Input | Arity | Denominator | Numerator at every `j : Fin 1` |
| --- | --- | --- | --- |
| `laurentUpper f` | `1` | `1` | `f` |
| `laurentLower f` | `1` | `f` | `1` |

The names record an upper and lower bound on the value of `f`. The respective
`no_common_zero` proofs use the denominator one and the numerator at index
zero: every multiplicative spectrum point sends one to the nonzero real
number one. No inverse of `f` or nonvanishing assumption on `f` is supplied.
The six projection lemmas ending in `_arity`, `_denominator` and `_numerator`
give these exact input formulas.

The pointwise locus laws are

```text
mem_locus_laurentUpper:
  x ∈ (laurentUpper f).locus ↔ x f ≤ 1
mem_locus_laurentLower:
  x ∈ (laurentLower f).locus ↔ 1 ≤ x f
```

The proofs unfold the existing rational inequalities and use `x 1 = 1`.
`mem_laurentUpper_or_mem_laurentLower` applies totality of the real order to
`x f` and `1`. Its set form,
`locus_laurentUpper_union_laurentLower`, identifies the union with the entire
actual spectrum.

For every bounded `K`-algebra homomorphism `φ : P → Q`,
`pullback_laurentUpper` and `pullback_laurentLower` prove equalities of
rational input data:

```text
(laurentUpper f).pullback φ = laurentUpper (φ f)
(laurentLower f).pullback φ = laurentLower (φ f)
```

These follow from the published `RationalData.pullback` constructor and
preservation of one by `φ`, including the proof fields by proof irrelevance.
Thus the pulled-back denominators and numerators are respectively
`(1, fun _ => φ f)` and `(φ f, fun _ => 1)`; the general
`locus_pullback` theorem gives the corresponding inverse-image equalities.

Over a complete coefficient field, the associated algebras and structural maps
are precisely the existing `(laurentUpper f).algebra`, `(laurentLower f).algebra`
and their `baseMap`s. Those constructors form the actual closed-ideal Tate
quotients of `P` with relations `1 * Y = f` and `f * Y = 1`, using the
existing series representatives. This module introduces no output carrier
and makes no new identification with a relative power-series presentation.

The overlap is the existing input
`(laurentUpper f).inter (laurentLower f)`. Its quotient algebra and the bounded
restrictions from the two factors are the existing `algebra`,
`interLeft ... .restriction` and `interRight ... .restriction`. The existing
`locus_inter` supplies the intersection of the two loci;
`mem_locus_inter_laurentUpper_laurentLower` specializes it to `x f = 1` by
antisymmetry. There is no separate overlap construction.

The constructors, pointwise formulas, cover law and pullback equalities need
no completeness assumption; the overlap lemma uses the existing complete-field
intersection interface. In particular, the requested complete fields include
trivially valued ones. The implemented proofs use only normalization at one,
preservation of one and order, with no small scalar or nontrivial valuation
argument. No nonzero or reduced hypothesis is imposed on `P` or `Q`. A zero
base has no normalized spectrum points, since its zero equals its one, so the
pointwise assertions and the union formula still hold for its empty spectrum.
The existing quotient and intersection interfaces retain zero and nonreduced
bases and empty loci. Both newly chosen numerator tuples have arity one;
the general rational-data interface and its empty tuples are unchanged.

This is a derived specialization of the published rational input definitions
and pullback/intersection constructions. Its source motivation is the binary
Laurent covering in Piotr Achinger, *Introduction to non-Archimedean Geometry*,
November 22, 2020, §7.1, printed/PDF p.64, immediately preceding Proposition
7.1.1. The source gives the two inequalities and the presentations
`A⟨X⟩/(X-f)` and `A⟨Y⟩/(fY-1)`. Registered source:
`achinger-2020-non-archimedean-geometry-nov22`, retained file
`literature/Piotr Achinger, Introduction to non-Archimedean Geometry (November 22, 2020).pdf`,
SHA256 `666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
Achinger's standing convention on printed/PDF p.6 assumes nontrivial scalar
valuation. The extension here to trivial valuation and to actual Berkovich
spectrum points is justified by the elementary proofs above, rather than
quoted from that convention or from the analytic exactness argument.

Rational-domain context and the Laurent/rational intersection relation are
from Vladimir G. Berkovich, *Non-archimedean analytic spaces*, Trieste lectures,
2009, Exercise 2.2.2(i)–(iii), printed/PDF p.9. Registered source:
`berkovich-2009-trieste-analytic-spaces`, retained file
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The source permits positive radii; this module specializes all radii to one
and reuses the Library's presented strict affinoids. No source-specific
errata file was present in the checked public errata locations on 2026-10-26.
No analytic exactness, unique gluing, or extension of the existing strict-test
representation property to all affinoid tests is asserted.
