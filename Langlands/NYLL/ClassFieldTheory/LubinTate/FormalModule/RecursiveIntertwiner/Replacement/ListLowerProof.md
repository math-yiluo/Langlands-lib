# NYLL M353.034: list replacement preserves lower-degree coefficients

The theorem `Langlands.NYLL.PortInternal.M353.d034` proves the published
proposition `Langlands.NYLL.PortInternal.M353.d034Statement`.
It is adapted from Naganori Yamaguchi's private theorem
`LubinTate.SameUniformizer.coeff_replaceList_eq_of_degree_lt`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
lines 580–609, at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`.

The readable pinned original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered snapshot collection
`external-lean-reuse-snapshots-2026-10-21` has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` registers the same pinned
project. No applicable NYLL erratum was found in the Library's
`notes/errata/`.

## Exact scope

The source section parameters at lines 29–38 are retained as implicit
`{K : Type u} [Field K]`, `{F : LocalField.{u, v} K}` and
`{sigma : Type w} [Fintype sigma]`, with three independent universes.
These are followed by implicit `{L : sigma → F.valuationSubring}` and
`{m : ℕ}`, then explicit `hm : 2 ≤ m`, `target`, `ds`, `H`,
`q : sigma →₀ ℕ` and `hq : q.degree < m`, in source order.
The source's unused section parameter `pi` does not occur in the theorem.

The coefficient ring is the actual valuation subring of the chosen
`LocalField`. The arbitrary series `target` has no prescribed-linear-term
hypothesis. The accumulator `H : d002 L` is the published subtype of
series having linear term `L`. The list
`ds : List {d : sigma →₀ ℕ // d.degree = m}` can have repetitions.
The conclusion is exactly

```text
MvPowerSeries.coeff q (d031 hm target ds H).1 =
  MvPowerSeries.coeff q H.1.
```

Here `d031` is the actual left fold of `d030` over the given list.
The exponent `q` is a raw finitely supported exponent, with its degree
restricted only by `hq`. There is no uniformizer witness,
`LubinTateSeries` parameter, enumeration hypothesis or nodup hypothesis.

## Implemented proof

The initial `change` unfolds the Statement abbreviation to its coefficient
equality. Induction on `ds` generalizes the bundled accumulator `H`.
The empty list case is reflexive, because its left fold returns `H`.

For a head exponent `d` of degree `m`, suppose `q = d.1` and apply total
degree to that equality. The resulting equality, `d.2` and `hq` contradict
one another by `omega`, giving `q ≠ d.1`. Unfolding the left fold at the
head identifies the new accumulator as `d030 hm target H d`.
The induction hypothesis applied to this accumulator reduces the goal to
one replacement step. Its underlying series is

```text
H.1 + MvPowerSeries.monomial d.1
  (MvPowerSeries.coeff d.1 target - MvPowerSeries.coeff d.1 H.1).
```

Unfolding `d030` and simplifying with
`MvPowerSeries.coeff_monomial_ne hqd` makes this coefficient equal to
`MvPowerSeries.coeff q H.1`. This follows the original proof at
lines 589–609. It uses the monomial coefficient formula directly, without
a separate single-step coefficient-law proof.

## Adaptations and attribution

Worker 294 prepared the source-adapted proof in the shared revision-2
draft of Task 6116. Worker 241 reused that preparation, compared it with
the pinned original and the published target and definitions, expanded
this documentation, and prepared the exact proof submission.
Worker 294 is credited as a coauthor of that submission.

The original private theorem becomes the public port-internal name
`Langlands.NYLL.PortInternal.M353.d034`. Source-private `Approximation`,
`replacementStep` and `replaceList` become the published `d002`, `d030`
and `d031`. Opened namespaces are qualified by `Langlands.NYLL`.
The source equality conclusion is expressed as the exact
`d034Statement` application, then unfolded by `change`; the rest of the
mathematical proof is unchanged.

The original broad `DegreeStabilization` and `RecursiveCorrection`
imports are replaced by the single published
`Replacement.ListStatements` import. It provides the actual replacement
definitions and the named proposition. The target's Lean/Markdown pair
and all its imported project pairs remain unchanged. No patch10 edit
affects this source module.

The original 2026 Naganori Yamaguchi copyright, Apache-2.0 release and
authorship header are retained verbatim. The existing
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged.
