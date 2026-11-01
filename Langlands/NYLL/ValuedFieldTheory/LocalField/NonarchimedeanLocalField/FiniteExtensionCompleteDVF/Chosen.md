# A chosen complete discrete valuation on a finite local extension

This module adapts exactly M248.006,
`LocalFieldTheory.chosenLocalExtensionCompleteDVF`, from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`, lines 130–138](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L130-L138),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Its adapted name is
`Langlands.NYLL.LocalFieldTheory.chosenLocalExtensionCompleteDVF`, in module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Chosen`.
It is a noncomputable structural definition. It selects one `CompleteDVF` on
`L` and states no theorem.

## Parameters and result

The definition has no universe parameters. Its complete parameter telescope is
that of the source:

```
(K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

The result is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{0,0} L`,
so the value group of the returned bundle also lies in `Type 0`.

Both fields lie in `Type 0`, as in the source. `K` is a nonarchimedean local
field in Mathlib's sense (`IsNonarchimedeanLocalField K`), with its supplied
valuative relation and supplied topology. `L` is an arbitrary field. The
algebra `K → L` is arbitrary supplied data, finite-dimensional and separable.
The definition places no further structure on `L`: no valuation, valuative
relation, topology, uniformity or local-field structure. It assumes no
extension certificate, no integral-closure witness and no other mathematical
premise, and it declares no instance. The identity extension is included:
for `L = K` with `Algebra.id`, Mathlib supplies `FiniteDimensional K K` and
`Algebra.IsSeparable K K`, so `chosenLocalExtensionCompleteDVF K K` is a
`CompleteDVF.{0,0} K`.

## Witness selection

The definition is

```
Classical.choose
  (exists_integralClosure_standard_completeDVF_extension.{0, 0, 0}
    K L (localCompleteDVF K))
```

The two names are published Library declarations:

- `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K : CompleteDVF.{0,0} K`
  is the canonical complete discrete valuation of `K` (adapted M248.001). Its
  value group is `ValuativeRel.ValueGroupWithZero K`, and its valuation is
  the canonical `ValuativeRel.valuation K`.
- `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF_extension`
  proves the closed proposition
  `ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u,v,w}`, the
  existence part of source theorem M245.018.

The theorem is applied at universes `0, 0, 0`, with this `K` and `L`, the
supplied algebra, the supplied finite-dimensionality and separability
instances, and `base := localCompleteDVF K`. The resulting proof has type

```
∃ target : CompleteDVF.{0,0} L,
  ∃ hExt : Valuation.HasExtension (localCompleteDVF K).valuation
      target.valuation,
    letI : Valuation.HasExtension (localCompleteDVF K).valuation
        target.valuation := hExt
    IsIntegralClosure target.valuation.valuationSubring
      (localCompleteDVF K).valuation.valuationSubring L
```

The definition is the `Classical.choose` of this existential. Here
`HasExtension` is Mathlib's `Valuation.HasExtension`. Under the installed
`hExt`, Mathlib's `Valuation.HasExtension.instAlgebra_valuationSubring`
supplies the algebra from the base valuation subring to the target valuation
subring. Both subrings map into the supplied `L` by their actual inclusions,
the base one through `K` and the supplied `algebraMap K L`.

When Lean compiles the definition, it moves the proof argument into the
automatically generated auxiliary theorem
`chosenLocalExtensionCompleteDVF._proof_1`. That theorem has exactly the type
displayed above, quantified over the telescope. Its value is
`exists_integralClosure_standard_completeDVF_extension.{0, 0, 0} K L (localCompleteDVF K)`.
The definition's elaborated body is
`fun K L _ _ _ _ _ _ _ _ => Classical.choose (chosenLocalExtensionCompleteDVF._proof_1 K L)`.
By proof irrelevance this equals the `Classical.choose` above, and `rfl`
proves the equality. The value of `Classical.choose` depends only on the
predicate, not on its proof.

Later properties are therefore available by `Classical.choose_spec` on that
same existential, for this same chosen target:

- `Classical.choose (Classical.choose_spec h)` is a
  `Valuation.HasExtension (localCompleteDVF K).valuation
  (chosenLocalExtensionCompleteDVF K L).valuation`;
- with that witness installed, `Classical.choose_spec (Classical.choose_spec h)`
  proves `IsIntegralClosure`. The two rings are the valuation subring of
  `chosenLocalExtensionCompleteDVF K L` and that of `localCompleteDVF K`,
  in `L`.

Here `h` is the specialized application above. This module states neither
fact as a declaration.

## Original-to-adapted declaration map

| Source unit | Source declaration (lines) | Adapted counterpart |
| --- | --- | --- |
| M248.001 | `LocalFieldTheory.localCompleteDVF` (34–55) | `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`, published separately and used as the base |
| M245.018 | `exists_integralClosure_standard_fundamental_identity` (`FiniteIntegralClosure.lean`, 631–685) | existence part published separately as `ExistsIntegralClosureStandardCompleteDVFExtensionStatement` with proof `exists_integralClosure_standard_completeDVF_extension` |
| M248.005 | private `chosenLocalExtensionCompleteDVF_exists` (114–128) | no separate declaration; replaced by the specialized application above |
| M248.006 | `chosenLocalExtensionCompleteDVF` (130–138) | `Langlands.NYLL.LocalFieldTheory.chosenLocalExtensionCompleteDVF` (this module) |

## Differences from the source

- **Direct specialization replaces the private wrapper.** The source defines
  the target as `Classical.choose (chosenLocalExtensionCompleteDVF_exists K L)`.
  That private theorem (M248.005) obtains a target, an extension witness, an
  integral-closure witness and a fundamental-identity witness from M245.018
  at `base := localCompleteDVF K`. It then discards the fundamental identity.
  Here no wrapper theorem is declared. The published existence theorem, which
  omits the fundamental-identity conjunct, is applied directly to the same
  base.

  The M248.005 proposition and the specialized published proposition differ
  only in spelling. The source writes the valuation subrings with the
  `CompleteDVF.valuationSubring` abbreviation. The published statement writes
  `target.valuation.valuationSubring` and
  `(localCompleteDVF K).valuation.valuationSubring`. A private check (below)
  wrote the source's M248.005 existential in its projection spelling and
  proved it from the published theorem. The `Classical.choose` of that proof
  equals this definition by `rfl`, so the definition chooses from the same
  predicate as the source.
- The namespace is prefixed with `Langlands.NYLL`.
- The source imports `NonarchimedeanLocalField.Basic`,
  `Mathlib.Algebra.Order.Hom.Units`, `Mathlib.NumberTheory.LocalField.Basic`,
  the NYLL `FiniteIntegralClosure` module and `ValuedAdicComplete`. They are
  replaced by the two published modules supplying the two names used:
  - `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`
    (`localCompleteDVF`; it also brings in
    `Mathlib.NumberTheory.LocalField.Basic` and `CompleteDVF`);
  - `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionProof`
    (the existence theorem and its statement, which bring in
    `FiniteDimensional`, `Algebra.IsSeparable`, `IsIntegralClosure` and
    `Valuation.HasExtension`).

  No external NYLL repository module is imported.
- The source opens `scoped ValuativeRel` and declares universes `u v y`.
  Neither is used here, since the definition is in `Type 0` throughout, and
  both are omitted. The source universes belong to other units of the file.

## Properties left to later units

Publishing this definition accepts only the chosen structural data. These
source units of the same file remain separate Prop targets with their own
proofs. Their proofs can use `Classical.choose_spec` on the existential
above.

- M248.007, `chosenLocalExtensionCompleteDVF_hasExtension`: the chosen
  valuation extends the valuation of `localCompleteDVF K`.
- M248.008, `chosenLocalExtensionCompleteDVF.instHasExtension`: the
  corresponding instance. No global `HasExtension` instance is declared
  here.
- M248.009, `chosenLocalExtensionCompleteDVF_isIntegralClosure`: the chosen
  valuation subring is the actual integral closure of the base valuation
  subring in `L`.
- M248.010, `chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite`:
  that ring is a finite module over the base valuation subring.
- M248.011, `chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension`:
  the valuation extension is unique.

Also outside this unit are comparison with an independently supplied
valuation on `L`, the fundamental identity of M245.018 for the chosen target,
the canonical integer-ring comparisons M248.003–M248.004, and the host
inertia and finite `Type 0` reciprocity results.

## Development checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Declaration inspection reports a definition with no level parameters. It
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

A separate private check module, not submitted, did the following:

- It printed the definition's type with universes. The telescope and the
  `CompleteDVF.{0,0} L` result were exactly those shown above.
- It printed the elaborated body and the auxiliary theorem, with the type
  and value described in the witness-selection section.
- It checked by `rfl` that the definition equals the displayed
  `Classical.choose` term.
- It recovered the `HasExtension` witness and, with it installed, the
  `IsIntegralClosure` witness by `Classical.choose_spec`. Both the source's
  projection spelling and the published expanded spelling were checked.
- It derived the source M248.010 conclusion `Module.Finite` from these
  witnesses with `IsIntegralClosure.finite`.
- It proved the source-form M248.005 existential and checked the `rfl`
  equality with its `Classical.choose`.
- It elaborated the identity case `chosenLocalExtensionCompleteDVF K K`.

These checks establish compilation and the correspondence stated here.
Semantic review and publication are separate steps.

## Attribution and modifications

The complete 206-line original was read. Its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The source-specific context is the namespace at line 24, universes at line
30, M248.005 at lines 114–128, M248.006 at lines 130–138, and the downstream
units M248.007–M248.011 at lines 140–206. The M245.018 theorem is in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`,
lines 631–685, file SHA256
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source partition records no patch10 compatibility edit for M248. No
applicable source erratum was found in the checked project and Library notes
on 31 October 2026.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The source is
Apache-2.0. The inherited, unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply. Their SHA256 values
are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE has no entry for the selected source file.

The source uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This adaptation uses the approved
environment above.

On 31 October 2026, Worker 785 extracted the single definition, made the
namespace, import and direct-specialization changes listed above, and wrote
this explanation. Worker 106 supplied routing only. The published inputs are
`localCompleteDVF` (adapted by Worker 785), the existence statement (adapted
by Worker 384) and its proof (Worker 785); they are imported by Lean name. No
unpublished implementation or draft from another worker was reused.
