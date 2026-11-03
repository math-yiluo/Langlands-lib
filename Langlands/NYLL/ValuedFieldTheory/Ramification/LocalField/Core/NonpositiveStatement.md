# Nonpositive local ramification laws

This module states together the four laws M327.017–M327.020 from Naganori
Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean#L877-L959).
It uses the already published
[`localLowerRamificationGroup` and `localUpperRamificationGroup`](Definitions.md).
This is a statement definition returning `Prop`; a proof of this exact closed
proposition belongs to a separate unit after statement publication.

## Complete proposition

The sole import is
`Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions`.
Inside `Langlands.NYLL.RamificationTheory.LocalField`, with
`open Langlands.NYLL.LocalFieldTheory`, the entire declaration is:

```lean
def LocalNonpositiveRamificationLawsStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    (∀ (t : ℝ), t ≤ 0 →
      localUpperRamificationGroup K L t = localLowerRamificationGroup K L t) ∧
    (∀ (t : ℝ), -1 < t → t ≤ 0 →
      localLowerRamificationGroup K L t = localLowerRamificationGroup K L 0) ∧
    (∀ (t : ℝ), -1 < t → t ≤ 0 →
      localUpperRamificationGroup K L t = localUpperRamificationGroup K L 0) ∧
    (∀ (t : ℝ), t ≤ -1 → localUpperRamificationGroup K L t = ⊤)
```

The declaration has no external parameters or universe parameters. Both fields
are in `Type` (universe 0). All eight supplied structures are quantified inside
the proposition: the two field structures, the algebra structure, finite
dimensionality, the Galois property, the base valuative relation, the base
topology and the nonarchimedean local-field property. Each clause quantifies
every real index it uses. The finite-Galois local-base telescope and every
endpoint inequality are preserved from the corresponding source theorem.

The first clause asserts equality of upper and lower numbering for every
`t ≤ 0`. The second and third assert constancy on the half-open interval
`(-1, 0]`, with value the respective group at index zero. In particular, the
source suffix `eq_zero` denotes equality with the index-zero group. It does
not assert that this group is the trivial subgroup. The fourth clause includes
the endpoint `-1`: every `t ≤ -1` has upper group equal to the full subgroup
`⊤` of the actual Galois group.

## Exact original-to-adapted clause map

Every original name in the following table lies in
`RamificationTheory.LocalField` in the pinned `Core.lean`. Every adapted
clause lies in the displayed closed
`Langlands.NYLL.RamificationTheory.LocalField.LocalNonpositiveRamificationLawsStatement`.

| Source unit, original declaration and lines | Adapted clause, in order |
| --- | --- |
| M327.017, `localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos`, 879–890 | 1: `∀ (t : ℝ), t ≤ 0 → localUpperRamificationGroup K L t = localLowerRamificationGroup K L t` |
| M327.018, `localLowerRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos`, 894–926 | 2: `∀ (t : ℝ), -1 < t → t ≤ 0 → localLowerRamificationGroup K L t = localLowerRamificationGroup K L 0` |
| M327.019, `localUpperRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos`, 929–943 | 3: `∀ (t : ℝ), -1 < t → t ≤ 0 → localUpperRamificationGroup K L t = localUpperRamificationGroup K L 0` |
| M327.020, `localUpperRamificationGroup_eq_top_of_le_neg_one`, 947–959 | 4: `∀ (t : ℝ), t ≤ -1 → localUpperRamificationGroup K L t = ⊤` |

The common telescope is shared by the conjunction. The source's explicit
hypotheses `(ht : t ≤ 0)`, `(hneg : -1 < t)` and `(ht : t ≤ -1)` become the
corresponding implications. Their order and logical content are unchanged.
There is no strengthening or weakening of a clause.

## Actual groups and dependency boundary

The two groups are the published definitions in `Core.Definitions`, with
values in `Subgroup Gal(L / K)`, where `Gal(L / K)` is the actual algebra
automorphism group `L ≃ₐ[K] L`. They use the canonical base DVF
`(Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).toDVF`
and the named chosen extension DVF
`(Langlands.NYLL.LocalFieldTheory.chosenLocalExtensionCompleteDVF K L).toDVF`.
The lower group is the published real lower ramification group for these
valuations. The upper group uses the actual inverse Herbrand function for
the same valuations.

As described in [the definitions' companion](Definitions.md), each imported
definition installs the extension witness locally from the proved
`chosenLocalExtension_properties K L` and uses the proved
`chosenLocalExtension_uniqueValuationExtension.{0} K L` directly. This
statement adds no valuation or topology on `L`, no `HasExtension` or uniqueness
premise, and no integral-closure, finite-module or inverse-law premise. It
introduces no instance or alias and leaves all published dependency
Lean/Markdown pairs unchanged.

The private source lemma M327.016,
`localInverseHerbrandFunction_eq_self_of_nonpos`, lines 846–875, is a possible
helper for a later proof. Its claim and proof are not extracted here.
The source-order edges in the
[M327 partition](../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m327)
are planning information; this statement needs only the already published
group definitions. This unit supplies no residue-kernel equality, filtered
reciprocity, host inertia, arbitrary-universe reciprocity, cup-comparison or
Weil-system result.

## Provenance and actual modifications

The source provenance is the four original public theorem statements listed
above. The original header and telescope at lines 1–134 and the complete
passage at lines 846–960 were read directly. The whole source file has SHA-256
`d0e79ce27df3b1f7481d2e6c89473f600acaf21f0cf4b678e29ba97a90792ecb`.
The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
followed by the source path above.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory was present
when this extraction was prepared.

The changes from the pinned source are:

1. Extract the conclusions and complete telescopes of exactly the four public
   laws into one closed Prop-valued `def`, with a shared universally quantified
   field and structure telescope and the four clauses in source order.
2. Prefix the namespace with `Langlands.NYLL` and retain only the
   `Langlands.NYLL.LocalFieldTheory` opening needed for the local-field class.
3. Replace the source's seven wholesale imports by the sole published
   `Core.Definitions` import. Reuse its actual group definitions unchanged.
4. Omit the original theorem proofs, private helper, other source declarations
   and unused `noncomputable section`, scoped opening and universe declaration.
   No proof or new theorem is introduced.

The [public port plan](../../../../../../notes/reuse/nyll-public-port-plan.md)
flags compatibility patch P5 for this source module. P5 changes original
line 693 in a restriction proof, outside all four extracted laws.
This statement extraction does not use Worker 25's later restriction-proof
adaptation.

## License and authorship

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi
([upstream author](https://github.com/n-yamaguchi-0729)), all rights reserved;
authors Naganori Yamaguchi (assisted by OpenAI Codex). Apache-2.0 applies.
The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), including their inherited
notices, are preserved unchanged. They match the pinned source copies;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The exact `Core.lean` path is not among NOTICE's listed third-party files.

Worker 106 contributed the source extraction, exact proposition design and
dependency analysis. Worker 60 checked the source and published interfaces,
implemented this statement extraction and wrote this companion on
3 November 2026. The Lean header records the modifications.
The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; the original source used
Lean 4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
