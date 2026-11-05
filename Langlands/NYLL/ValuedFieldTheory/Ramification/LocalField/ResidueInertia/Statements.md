# Zero-depth local ramification groups and the actual residue-action kernel

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.LocalField.LocalRamificationZeroResidueKernelStatement`.
It extracts the conclusions and full common hypotheses of NYLL source
theorems M328.001 and M328.002. Its sole exported declaration has type
`Prop`, with no declaration parameters or universe parameters. Both fields
and all fourteen source instances are quantified inside the proposition.

## Complete proposition

Inside `Langlands.NYLL.RamificationTheory.LocalField`, with
`Langlands.NYLL.LocalFieldTheory` open and scoped `ValuativeRel` notation,
the complete definition is:

```lean
def LocalRamificationZeroResidueKernelStatement : Prop :=
  ∀ (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]],
    (localLowerRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) ∧
    (localUpperRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker)
```

The fields lie in `Type` (universe 0). For each field the proposition
quantifies a field structure, a valuative relation, a topology and a
nonarchimedean local-field instance, in that order. It then quantifies the
supplied `K`-algebra structure on `L`, finite-dimensionality, the Galois
condition, extension of the canonical valuations, the integral-closure
condition on the supplied integer rings and finiteness of the extension
integer ring as a module over the base integer ring. These are precisely
the original fourteen instance binders, in their original order. The
valuation-extension, integral-closure and finite integer-module hypotheses
are retained even when they are not explicit arguments of every term in
the conclusion.

The first conjunct identifies the actual lower ramification group at real
index zero with the residue-action kernel. The second does the same for
the actual upper ramification group. The kernel is a subgroup of the
actual algebra automorphism group `Gal(L/K) = L ≃ₐ[K] L`; it consists of
automorphisms acting trivially on the residue field. Zero-depth
ramification is thus stated as this kernel equality, without any assertion
that the kernel is the trivial subgroup.

## Chosen valuation and supplied residue action

The two groups are reused from the published
[Core definitions](../Core/Definitions.md). Their base is the canonical
complete discretely valued field `localCompleteDVF K`, whose valuation is
`ValuativeRel.valuation K`. Their target is the named chosen extension
`chosenLocalExtensionCompleteDVF K L`, with its chosen valuation. Each
published group body obtains its extension witness locally from
`chosenLocalExtension_properties` and uses the published
`chosenLocalExtension_uniqueValuationExtension.{0}`. The group interface
itself requires no supplied valuation or topology on `L`.

The homomorphism is the published
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L`,
with type
`Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`; see the
[residue algebra definitions](../../../LocalField/NonarchimedeanLocalField/ResidueGalois/AlgebraDefinitions.md).
Here `𝒪[F]` is the integer ring of the supplied
`ValuativeRel.valuation F`, and `𝓀[F]` is its actual residue field
`IsLocalRing.ResidueField 𝒪[F]`. The residue algebra structure is the one
induced by the supplied algebra and valuation-extension instance. The
homomorphism uses the published restriction to `𝒪[L]` and its induced
residue-field map. In particular, its residue field is built from the
supplied valuation on `L`.

The equalities compare groups constructed with the chosen extension
valuation to the residue action constructed with the supplied extension
valuation. The proposition retains the original assumptions for that
comparison; it does not identify the two valuations by definition or
replace either construction. No public instance, replacement data,
definition alias, extra premise or proof is added.

## Direct imports and scope

The only direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.AlgebraDefinitions`.

The first supplies the actual groups and their published dependencies.
The second supplies the actual residue algebra homomorphism and its
published dependencies. Both modules and their dependencies are unchanged.
No local proof of the comparison is included. A later proof must prove this
exact published target. Filtered reciprocity, host inertia comparisons,
finite Type 0 reciprocity and universe transport remain separate work.

## Author verification

The approved-environment `lean_check` completed successfully with zero
errors and warnings. Inspection of the complete unapplied declaration
reported kind `definition`, no level parameters and
`statement_returns_prop: true`; the declaration type is `Prop`.
The only reported axioms were `propext`, `Classical.choice` and
`Quot.sound`, inherited through the actual imported constructions.
The Lean definition was also compared verbatim to the target in the task
objective. These author checks establish compilation and the declaration
shape; independent semantic review and Integrator publication remain
separate requirements.

## Original-source correspondence

The original is Naganori Yamaguchi's *ClassFieldTheory (NYLL)*,
repository `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean).
The readable pinned copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Worker 1556 directly read all 113 lines and verified the full-file SHA-256:
`456328b412a0c609dd32b6b884b72ac84abef430d94c635c89f599ca4aa374ef`.

| Original declaration in `RamificationTheory.LocalField` | Precise original location | Conjunct of `LocalRamificationZeroResidueKernelStatement` |
| --- | --- | --- |
| M328.001 `localLowerRamificationGroup_zero_eq_residue_ker` | declaration line 30; telescope and conclusion lines 31–42; proof lines 43–94 | 1: lower group at zero equals the actual residue-action kernel |
| M328.002 `localUpperRamificationGroup_zero_eq_residue_ker` | declaration line 97; telescope and conclusion lines 98–109; proof lines 110–111 | 2: upper group at zero equals the same actual residue-action kernel |

Both source telescopes are identical. Closing their common telescope and
joining the lower conclusion followed by the upper conclusion is the only
mathematical packaging change. The original theorem proofs are omitted.
The namespace gains `Langlands.NYLL`, references resolve to the published
prefixed data declarations, and the original three broad imports are
replaced by the two focused imports above. Only the needed namespace
opening and scoped notation are retained. The original `noncomputable
section` is unnecessary for this proposition definition and is omitted.
The header and doc comments record the statement extraction. No patch10
edit is used: M328 is outside its nine changed modules.

The public source and feasibility audits and the
`notes/reuse/nyll-public-port/m313-m336.md` M328 rows provide navigation and
reuse context. They supply no proof or acceptance of this proposition.

## Provenance, license and authorship

The registered original is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory was
present when this extraction was checked on 4 November 2026.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), including the applicable
inherited third-party notices, are preserved unchanged. Their SHA-256 values
are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No third-party source is copied into this unit.

Worker 106 contributed the exact proposition design, original-source
extraction and reuse analysis. Worker 1556 checked the pinned original and
published interfaces, implemented this statement extraction and wrote its
companion Markdown on 4 November 2026. The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
