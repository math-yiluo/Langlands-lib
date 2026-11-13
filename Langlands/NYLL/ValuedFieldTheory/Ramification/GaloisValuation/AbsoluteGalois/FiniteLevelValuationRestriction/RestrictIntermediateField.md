# Restricting a valuation subring to an intermediate field

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.RestrictIntermediateField`
defines
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField`.
It adapts the definition M233.004 of Naganori Yamaguchi's
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`, lines 110–118](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean#L110-L118).
The complete original file has SHA-256
`bc2b582cac15fc4a9c6dc94e9687368e2a1bf91ca9d4111d41a9458fe8e49889`.
I read the whole original file (344 lines). That includes the ambient
`namespace RamificationTheory` at line 53, the `noncomputable section` at
line 60, the universes at line 62, `namespace ValuationSubring` at line 64,
section `RestrictIntermediateField` at line 110, its variables at line 112
and the definition at lines 114–118.

## The declaration

The definition has universe parameters `u` (base field) and `v` (ambient
field). Its full signature and value are:

```lean
def restrictIntermediateField
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    ValuationSubring E :=
  A.comap (algebraMap E Ω)
```

The binder kinds are those of the source:

- `K` and `Ω` are implicit;
- the field and algebra structures are instance binders;
- the valuation subring `A` and the intermediate field `E` are explicit, in
  that order.

`ValuationSubring` and `IntermediateField` are Mathlib's structures.
`algebraMap E Ω` is the inclusion of the intermediate field into `Ω`.

## Meaning

`restrictIntermediateField A E` is the preimage of `A` under the inclusion
`E → Ω`. It is formed with Mathlib's `ValuationSubring.comap`, which pulls a
valuation subring back along a ring homomorphism of fields. An element
`x : E` belongs to it exactly when its image `(x : Ω)` belongs to `A`, and
this holds by definition. So it is the valuation subring `A ∩ E` of `E`.

Because the declaration lives in the namespace
`Langlands.NYLL.RamificationTheory.ValuationSubring` and its first explicit
argument is a `ValuationSubring Ω`, the source's dot notation
`A.restrictIntermediateField E` works in a consumer namespace that opens
`Langlands.NYLL.RamificationTheory`. I checked this with `lean_check`, using
`A.restrictIntermediateField E` inside `Langlands.NYLL.LocalClassFieldTheory`
under `open RamificationTheory`, as the NYLL consumers do.

## Source correspondence and modifications

| Source item | Adapted item |
| --- | --- |
| `namespace RamificationTheory` (53), `namespace ValuationSubring` (64) | `namespace Langlands.NYLL.RamificationTheory`, `namespace ValuationSubring` |
| `noncomputable section` (60), `universe u v w z` (62) | `noncomputable section`, `universe u v` (the two the definition uses) |
| Section variables (112) | Unchanged |
| Definition M233.004 (114–118) | Unchanged, including its docstring |

Other modifications:

- The namespace gains the prefix `Langlands.NYLL`.
- Only the section variables the definition uses are kept.
- The upstream file's 38 imports are replaced by two focused Mathlib imports,
  `Mathlib.FieldTheory.IntermediateField.Basic` and
  `Mathlib.RingTheory.Valuation.ValuationSubring`.
- The source's `open ValuationTheory` and
  `open ValuationTheory.DiscreteValuationField.HenselianDVF` (55–56) are
  omitted. The definition does not use them, and with them omitted
  `ValuationSubring` can only mean Mathlib's structure.

This module contains only M233.004. Mathlib has no declaration that restricts
a valuation subring to an intermediate field, and the Library has no
declaration named `restrictIntermediateField`. The source's theorems about it
(M233.005–.007, .010) are stated in the sibling module `Statements`. The rest
of the source module is outside this unit: the power-membership lemmas
M233.001–.003, the translate lemmas M233.008–.009 and .011, and the
separable-power lemmas.

## Attribution

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the original path
above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
public port partition `notes/reuse/nyll-public-port/m217-m240.md` lists
M233.004 and records no patch10 change for this source module. The workspace
`notes/errata` directory has no entry for this source. The NYLL NOTICE does
not list this source file among its third-party paths.

Original copyright and authorship are kept: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean header records the modifications, made by Worker 122 on
13 November 2026. The approved environment is Lean 4.34.0 with Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
