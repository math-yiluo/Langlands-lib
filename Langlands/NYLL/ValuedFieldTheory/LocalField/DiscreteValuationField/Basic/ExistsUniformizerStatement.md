# Existence of a uniformizer in a local-field package: statement target (M334.008)

This module defines one closed proposition target in
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`:
`exists_uniformizerStatement.{u, v} : Prop`. It is the type of the source
theorem `exists_uniformizer` (unit M334.008). The complete source telescope
is universally quantified inside the proposition in its original order and
with its original binder kinds: implicit `{K : Type u}`, instance
`[Field K]` and explicit `(F : LocalField.{u, v} K)`. Universe parameters
`u v` are arbitrary and independent, in the source order. This file
supplies the statement only. Its proof is a separate `lean.proof@1` task,
whose theorem keeps the source name `exists_uniformizer`.

## Complete proposition

```lean
def exists_uniformizerStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K)
```

For every field `K` in universe `u` and every local-field package
`F : LocalField.{u, v} K`, there is an element `pi` of the valuation subring
of `F` whose image `(pi : K)` in `K` is a uniformizer of the chosen
valuation `F.toCompleteDVF.valuation : Valuation K F.ValueGroup`.

`LocalField` is the published shared structure. It packages a chosen
complete discrete valuation on `K` with value group in universe `v`
(the parent `CompleteDVF.{u, v} K`) together with finiteness of the residue
field. `LocalField.valuationSubring F` is the published reducible
abbreviation for `F.toCompleteDVF.valuationSubring`. The published
`CompleteDVF` projections read it along the path
`CompleteDVF → HenselianDVF → DVF` as the type underlying
`Valuation.valuationSubring` of the stored valuation. It is
definitionally the valuation subring of `F.toCompleteDVF.valuation`, and
`(pi : K)` is the subtype coercion `Subtype.val` into `K`. These
abbreviations come from the published `LocalField.Basic.Definitions`
module and the `CompleteDVF` modules it imports.

`Valuation.IsUniformizer` is Mathlib's predicate
(`Mathlib.RingTheory.Valuation.Discrete.Basic`). For a valuation `v` with
an `IsRankOneDiscrete v` instance `hv`, `v.IsUniformizer π` means
`v π = hv.generator`, the chosen generator `< 1` of the value group.
Here the instance is not an extra hypothesis. Instance search obtains it
as the published instance
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete.isRankOneDiscrete`
applied to the stored instance field `CompleteDVF.instCompleteDiscrete` of
the `CompleteDVF` parent of `F`. A development check confirmed this. The
source elaborates the same way. No hypothesis is added and the conclusion is unchanged. In
particular, the residue-finiteness field of `F` is present but not needed for
the statement to make sense.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean#L73-L76).
The original file SHA-256 is
`69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`, checked
against the readable copy. That copy is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The recorded patch10 does not change this source module.

| Unit | Original name | Source lines | Adapted target |
| --- | --- | --- | --- |
| M334.008 | `LocalFieldTheory.DiscreteValuationField.LocalField.exists_uniformizer` | docstring 73, type 74–75, proof 76 | `exists_uniformizerStatement` |

The source declaration is

```lean
/-- A local field package has a uniformizer. -/
theorem exists_uniformizer (F : LocalField.{u, v} K) :
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K) :=
  F.toCompleteDVF.exists_uniformizer
```

It uses the section variables `{K : Type u} [Field K]` (line 42) in namespace
`LocalFieldTheory.DiscreteValuationField.LocalField`, with
`open ValuationTheory.DiscreteValuationField` (line 31) and
`universe u v w x` (line 27). The target quantifies the two section variables
first and then the explicit `F`, which is the source theorem's elaborated
type. The body `∃ pi : F.valuationSubring,
F.toCompleteDVF.valuation.IsUniformizer (pi : K)` is copied verbatim. Its
names resolve to the published adapted declarations
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`,
`LocalField.valuationSubring` and `LocalField.toCompleteDVF`. They also
resolve to `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.valuation`
and to Mathlib's `Valuation.IsUniformizer`.

The source proof (line 76) calls `CompleteDVF.exists_uniformizer`
(source unit M107.022). That theorem is not part of this target and is not
needed to state it.

## Adaptation and reuse

Worker 486 made these modifications on 14 November 2026:

- extracted the type of M334.008 only, omitting the proof (line 76) and
  all other source declarations;
- prefixed the namespace with `Langlands.NYLL` and suffixed the name with
  `Statement`;
- moved the complete source telescope, including the section variables
  `{K : Type u} [Field K]`, into the body of a Prop-valued definition with
  explicit universe parameters `.{u, v}` in the source order;
- replaced the nine upstream imports by the one published import below;
- dropped the `open ValuationTheory.DiscreteValuationField` line and the
  unused universes `w x`. The body needs neither, because it uses only
  `LocalField` projections inside the `LocalField` namespace;
- wrote a new module docstring and declaration docstring, added the
  modification notice in the Lean header, and wrote this paired Markdown.

The formula, binder kinds and order are unchanged. No instance, simp
attribute or other declaration is introduced.

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`.
It supplies the published `LocalField` package and its `valuationSubring`
abbreviation. Transitively, through the published `CompleteDVF` modules, it
also supplies `Mathlib.RingTheory.Valuation.Discrete.Basic`, which declares
`Valuation.IsUniformizer`.

The published Library and the approved Mathlib were searched before
authoring. Neither declares this target, and the Library does not declare
`CompleteDVF.exists_uniformizer`. Mathlib's
`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial` is the expected
proof ingredient for the separate proof task. It is not needed to state the
target.

## Attribution

The original copyright, Apache-2.0 release line and author header are
retained verbatim, followed by a modification notice. The unmodified
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file.
