# NYLL M353.030–031: prescribed-degree coefficient replacement

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

## Source declarations and data

| Unit | Original private declaration | Source lines | Adapted declaration |
| --- | --- | --- | --- |
| M353.030 | `LubinTate.SameUniformizer.replacementStep` | 532–544 | `Langlands.NYLL.PortInternal.M353.d030` |
| M353.031 | `LubinTate.SameUniformizer.replaceList` | 547–554 | `Langlands.NYLL.PortInternal.M353.d031` |

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

`d030` retains implicit `L` and `m`, followed by explicit `hm : 2 ≤ m`,
`target`, bundled accumulator `H : d002 L`, and
`d : {d : sigma →₀ ℕ // d.degree = m}`. It returns another `d002 L`.
Its underlying series is precisely

```text
H.1 + monomial d.1 (coeff d.1 target - coeff d.1 H.1).
```

The subtype certificate applies the exact published theorem
`Langlands.NYLL.PortInternal.M353.d029` to `H.2`, `d.1` and this
coefficient difference. Its degree hypothesis follows from `d.2` and `hm`
by the same `omega` proof as the source. Thus the construction preserves
the prescribed linear term without using a property of `target`.
The exact proof is imported from `Replacement.LinearTermProof`, rather
than obtained from the proposition target alone.

`d031` retains implicit `L` and `m`, then explicit `hm`, `target`,
`ds : List {d : sigma →₀ ℕ // d.degree = m}` and `H`, in that order.
It returns `ds.foldl (d030 hm target) H`. The order of replacements is
the given list order; neither a nodup condition nor a chosen enumeration
is required for this data. The separate coefficient-law targets state
which coefficients are assigned and retained.

## Adaptations and dependencies

Worker 294 extracted both complete definitions into the focused
`Replacement.Definitions` module, changed their source-private names to
the required public port-internal names, and qualified opened namespaces
by `Langlands.NYLL`. The source bodies and docstrings are retained after
renaming `Approximation` to `d002` and `hasLinearTerm_add_monomial` to
`d029`, and the call from `replaceList` to `replacementStep` to `d030`.
The noncomputable section and independent universe declarations remain.

The original broad `DegreeStabilization` and `RecursiveCorrection` imports
are replaced by the published `Approximation.Definitions` and
`Replacement.LinearTermProof` modules. A focused Lean check of this module
verifies their sufficiency. Neither recursive-series data nor the
monomial-correction construction is used. No new instance, axiom or
coefficient law is introduced here.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
