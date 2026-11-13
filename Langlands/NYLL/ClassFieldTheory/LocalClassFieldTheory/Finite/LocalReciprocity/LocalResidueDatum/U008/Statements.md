# The chosen separable valuation extends the local valuation: target

This module states NYLL source unit M249.008 as a closed proposition. The
source declaration is an `instance` whose class is a proposition. The module
exports one Prop-valued `abbrev`,
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationHasExtensionStatement`.
Nothing is proved here, and no instance is installed. The proof is a separate
unit under the adapted source name
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationHasExtension`.
That unit registers the proof as a global instance, as in the source.

Mathematically, the target says: for a nonarchimedean local field `K`, the
valuation of the chosen valuation ring of the separable closure extends the
canonical discrete valuation of `K`. Restricted to `K`, it is equivalent to
the canonical valuation. In the source, later parts of the finite local
reciprocity construction use this instance, among them the decomposition
group statements and the local residue datum M249.024.

## The proposition

```lean
abbrev localSeparableValuationHasExtensionStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation.HasExtension
      (localSeparableValuationSubring K).valuation
```

There is no level parameter: `K` lives in `Type`, as in the source. The
quantified binders, in order, are the section variables of the source (lines
45–46). The source instance has no parameters of its own.

| Binder | Meaning |
| --- | --- |
| `K : Type` | the base field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |

The conclusion is Mathlib's class `Valuation.HasExtension v w` for
`v = (localCompleteDVF K).valuation`, a valuation on `K`, and
`w = (localSeparableValuationSubring K).valuation`, a valuation on
`SeparableClosure K`. It is taken along Mathlib's algebra map
`K → SeparableClosure K`. `HasExtension v w` states that for all `x y : K`,
`v x ≤ v y` holds exactly when `w` of the image of `x` is at most `w` of the
image of `y`.

### Published declarations used

- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K`
  (M249.006, [definition](../U006/Definitions.md)): the preimage, under the
  inclusion `SeparableClosure K → AlgebraicClosure K`, of a valuation subring
  of `AlgebraicClosure K` chosen by Chevalley's extension theorem.
  `.valuation` is Mathlib's `ValuationSubring.valuation`.
- `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K` (M248.001,
  [the canonical complete DVF](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Canonical.md)):
  the canonical valuation of `K` packaged as a complete discrete valuation
  field. `.valuation` is that valuation, used at universe `0`.

The statement needs neither of the local instances M249.001 and M249.002.
`algebraMap K (SeparableClosure K)` comes from Mathlib's algebra structure on
the intermediate field over `K`.

### Why the target is an `abbrev`

The source registers M249.008 as a global instance. Following the Library's
convention for Prop-valued instances (for example M239.005 and M239.038 in
[the M239 statement targets](../../../../../../ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring/Statements.md)),
the target is a reducible `abbrev`. A theorem whose type is this target can
then be given `attribute [instance]`. Instance search unfolds the `abbrev` and
sees the `∀`-telescope ending in the class `Valuation.HasExtension`. A private
check confirmed this. A draft proof module declares
`theorem localSeparableValuationHasExtension : localSeparableValuationHasExtensionStatement`
followed by `attribute [instance] localSeparableValuationHasExtension`. A
client module then proves
`(localCompleteDVF K).valuation.HasExtension (localSeparableValuationSubring K).valuation`
by `inferInstance`.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings (diagnostic `8c5a9afe-edd4-4d12-9550-2fcd9fa1a210`,
against Library commit `aad41a6eb68efecf631ccac31f2e33766f3711f1`). Inspection
of the declaration reported kind `definition`, no level parameters,
`statement_returns_prop: true`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The draft proof and the client
`inferInstance` check compiled together with it (diagnostic
`5a517d6a-3847-48ff-80ac-0b5f251cf6c2`).

## Imports and scope

The only import is the published module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`.
It supplies `localSeparableValuationSubring` and, through its imports,
`localCompleteDVF`, Mathlib's `IsNonarchimedeanLocalField`, `SeparableClosure`
and `Valuation.HasExtension`.

Only M249.008 is stated. The analogous private instance M249.005 for the
auxiliary ring of `AlgebraicClosure K` (lines 78–84) is not stated. The
source theorem M249.007 cited in the source body is stated separately
([target](../U007/Statements.md)).

This module replaces the rejected candidate
`7630c44c-49e5-431e-a846-4067d234111f`, which proposed the instance with its
proof as a `lean.definition`. That policy requires a definition or defined
type, and an instance whose class is a proposition is a theorem.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L106-L113)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`, the
value recorded for M249 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m249).

| Partition unit | Original declaration in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M249.008 | instance `localSeparableValuationHasExtension` | 106–113 | `localSeparableValuationHasExtensionStatement` |

Line 106 is the doc comment, line 107 the instance name, lines 108–109 its
type, and lines 110–113 the source body. The source module opens namespace
`LocalClassFieldTheory` (line 31), opens `LocalFieldTheory` (line 35), works
in `noncomputable section` (line 39) and declares the section variables at
lines 45–46.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` prefix to the namespace. The chosen ring is the
  published prefixed definition of the same name. The source spells the
  canonical valuation `localCompleteDVF K`, relying on the opened namespace
  `LocalFieldTheory`. The adapted statement spells out the published name
  `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`;
- packaged the instance type as the closed proposition above, as a reducible
  `abbrev`. The section variables become the leading `∀`-binders, with the
  same kinds (explicit for `K`, instance-implicit for the rest);
- omitted the source body, the `instance` attribute and the source's `open`
  lines, which the statement does not need;
- replaced the source imports by the published module above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `LocalResidueDatum.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
