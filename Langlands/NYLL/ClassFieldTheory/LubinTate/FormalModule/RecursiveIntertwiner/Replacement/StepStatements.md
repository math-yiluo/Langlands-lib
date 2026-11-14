# NYLL M353.032–033: coefficients of one replacement step

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
The readable pinned source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered snapshot collection `external-lean-reuse-snapshots-2026-10-21`
has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` registers the same pinned project.
No applicable NYLL erratum was found in the Library's `notes/errata/`.

## Exact proposition targets

| Unit | Original private theorem | Signature lines | Public target |
| --- | --- | --- | --- |
| M353.032 | `LubinTate.SameUniformizer.coeff_replacementStep_self` | 556–563 | `Langlands.NYLL.PortInternal.M353.d032Statement` |
| M353.033 | `LubinTate.SameUniformizer.coeff_replacementStep_eq_of_ne` | 566–574 | `Langlands.NYLL.PortInternal.M353.d033Statement` |

All declarations retain the effective source section parameters from
lines 29–38: implicit `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}` and `{sigma : Type w} [Fintype sigma]`.
The three universes are independent. The unused source section parameter
`pi` does not occur in these declarations. There is no uniformizer witness
or `LubinTateSeries` parameter. The shared adapted `LocalField` extends the
published `CompleteDVF`; coefficients are in its actual `valuationSubring`.
The imported `d002 L` is exactly the subtype of series `H` satisfying
`HasLinearTerm H L`, where `H - linearForm L` has total order at least two.
The target series is arbitrary and has no prescribed-linear-term hypothesis.

Both targets retain implicit `L` and `m`, explicit `hm : 2 ≤ m`,
`target` and `H : d002 L`, in source order. `d032Statement` then takes
an explicit degree-`m` exponent `d`. Its proposition is

```text
coeff d.1 (d030 hm target H d).1 = coeff d.1 target.
```

`d033Statement` instead takes explicit degree-`m` exponents `q` and `d`,
in that order, followed by `hqd : q ≠ d`. It states

```text
coeff q.1 (d030 hm target H d).1 = coeff q.1 H.1.
```

Here `d030` is the actual replacement construction from
`Replacement.Definitions`: it adds the monomial at `d` with the
difference between target and current coefficients. The two propositions
specify the selected coefficient and a different coefficient in the same
total degree. They are conclusion-valued `abbrev`s with the original
hypothesis proofs retained as arguments, not asserted theorems. In
particular `hqd` is retained even though its proof term does not occur in
the equality. Separate exact proof successors must prove
`Langlands.NYLL.PortInternal.M353.d032` and `.d033` after target publication.
The original proof ranges are 564 and 575–578 respectively.

## Adaptations

Worker 294 extracted the two source signatures and equality conclusions,
renamed source-private references to `d002` and `d030`, qualified namespaces,
and replaced the original broad imports by the focused published
`Replacement.Definitions` import. The independent source universes and
binder kinds are unchanged. The theorem commands become Prop-valued
Statement abbreviations and omit their source proofs; local
`linter.unusedVariables false` wrappers retain proof arguments without
spurious unused-variable warnings. A focused declaration inspection checks
that each target returns `Prop`. These targets add no assumption on the
list program or on `target` and do not assert either coefficient law as a
proved fact.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
