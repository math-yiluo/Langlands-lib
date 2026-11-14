# Native finite abelian norm subgroup

This pair adapts NYLL unit M300.003: the norm subgroup of the actual fixed
field represented by a finite abelian subextension of the chosen separable
closure.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`,
lines 79–81, with its docstring at lines 77–78 and section parameters at
line 32. The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained original file has SHA-256
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`
and is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`
at the source path above.

| Unit | Original declaration | Adapted declaration |
| --- | --- | --- |
| M300.003 | `LocalClassFieldTheory.finiteAbelianNormSubgroup` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianNormSubgroup` |

The complete telescope and result are:

```lean
noncomputable def Langlands.NYLL.LocalClassFieldTheory.finiteAbelianNormSubgroup
    (K : Type) [Field K]
    (L : Langlands.NYLL.ClassFormation.FiniteAbelianSubextension
      (Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase K)) :
    Subgroup Kˣ
```

Both `K` and `L` are explicit, and the field instance is instance implicit.
The source uses `Type`, so `K` remains in universe zero. There are no
local-field, finite-dimensional, or Galois hypotheses in this telescope.
The Galois structure needed to form the fixed field inside
`SeparableClosure K` comes from Mathlib's separable-closure instances.
The result is a subgroup, hence data in `Type`, rather than a proposition
target.

The definition body is literally the source expression:

```lean
localNormSubgroup K (abstractFixedField K (SeparableClosure K) L.field)
```

Here `L.field` is the actual closed subgroup carried by the finite abelian
package; `abstractFixedField` is its fixed intermediate field inside
`SeparableClosure K`. The native `localNormSubgroup` is the range of the
algebra norm on units, so this is the subgroup of `Kˣ` formed by norms of
units of that fixed field.

The pair reuses these published declarations by Lean name:

| Declaration | Imported module |
| --- | --- |
| `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` and `.field` (M296.001–.002) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions` |
| `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` (M093.001) | `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions` |

These are the source package, base, fixed field and norm subgroup interfaces
with the `Langlands.NYLL` namespace prefix. In particular, the native
M093.001 norm subgroup has no finite-dimensional premise and is reused
directly. No instance or supporting definition is introduced here.

Worker 536 made the following modifications on 14 November 2026:

1. Extracted only M300.003, keeping its original docstring, `def` kind,
   noncomputable scope, explicit section parameter `(K : Type) [Field K]`,
   explicit `L`, result and body.
2. Prefixed `LocalClassFieldTheory` with `Langlands.NYLL`. Kept the used
   `LocalFieldTheory` and `ClassFormation` openings, which resolve to the
   corresponding adapted namespaces; omitted the unused
   `RamificationTheory`, `CyclicCohomology` and `KummerTheory` openings.
3. Replaced the five broad source imports with the four published data
   modules listed above. Omitted the rest of the source module, including
   the preceding finiteness and normality theorems: M300.003 does not use
   either theorem.
4. Replaced the whole-module overview with this focused overview and an
   explicit modification record; added this paired Markdown.

This pair supplies the definition only. The later openness, finite-index,
norm-comparison and order-embedding assertions remain separate units.

The original Apache-2.0 copyright and author header is retained verbatim.
The Library retains `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
The registered attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
