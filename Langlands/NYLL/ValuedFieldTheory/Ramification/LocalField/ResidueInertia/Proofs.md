# Zero-depth local ramification and the actual residue-action kernel

This module proves the published proposition
`Langlands.NYLL.RamificationTheory.LocalField.LocalRamificationZeroResidueKernelStatement`
and exposes the two NYLL M328 source-name consequences. The principal theorem's
entire type is:

```lean
theorem localRamificationZeroResidueKernel :
    LocalRamificationZeroResidueKernelStatement
```

It has no external parameters, universe parameters or added hypotheses.
The [unchanged published statement](Statements.md) quantifies `K L : Type`
and all fourteen original instances internally, and concludes first the lower
equality and then the upper equality. Both compare the actual groups at real
index zero with the kernel of
`galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L`.

## Exported consequences and hypotheses

All three theorems are in
`Langlands.NYLL.RamificationTheory.LocalField`.

| Callable theorem | Conclusion |
| --- | --- |
| `localLowerRamificationGroup_zero_eq_residue_ker K L` | `localLowerRamificationGroup K L 0 = (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker` |
| `localUpperRamificationGroup_zero_eq_residue_ker K L` | `localUpperRamificationGroup K L 0 = (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker` |

Each consequence takes `K L : Type` explicitly, followed by the same fourteen
instance binders as the source and statement, in this order:

1. `Field K`, `ValuativeRel K`, `TopologicalSpace K`,
   `IsNonarchimedeanLocalField K`;
2. `Field L`, `ValuativeRel L`, `TopologicalSpace L`,
   `IsNonarchimedeanLocalField L`;
3. `Algebra K L`, `FiniteDimensional K L`, `IsGalois K L`;
4. `Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`;
5. `IsIntegralClosure 𝒪[L] 𝒪[K] L`;
6. `Module.Finite 𝒪[K] 𝒪[L]`.

The alias proofs are respectively `.1` and `.2` of the principal theorem
applied to `K L`. They retain the entire source telescope, including module
finiteness even though the implemented argument does not explicitly invoke it.
Zero-depth ramification is the inertia kernel; the result makes no claim
that this subgroup is trivial.

## Implemented proof

The actual groups use the chosen extension valuation on `L`, whereas the
actual residue action uses the supplied valuation on `L`. The proof preserves
both constructions and the supplied algebra map.

First it installs only the local extension witness
`Classical.choose (chosenLocalExtension_properties K L)`, exactly as in the
published group bodies, and keeps their
`chosenLocalExtension_uniqueValuationExtension.{0} K L` witness.
It sets `target` to the chosen complete DVF's underlying DVF.
The second conjunct of the published
`chosenLocalExtension_suppliedComparison K L` identifies the actual chosen
and supplied valuation subrings in `L`. Applying `ValuationSubring.toSubring`
gives equality with `(ValuativeRel.valuation L).integer`, whose carrier is
`𝒪[L]`. `RingEquiv.subringCongr` supplies an identity-on-`L` ring equivalence
`eInteger : target.valuationSubring ≃+* 𝒪[L]`.

Two local comparisons implement the transport:

- `hmap` identifies the image under `eInteger` of the chosen-ring displacement
  with `galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (eInteger a) -
  eInteger a`. Subtype extensionality reduces this to equality in `L`.
  The proof uses
  `Higher.valuationSubringAutOfUniqueExtension_apply_coe` and the published
  `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply`, with all comparison
  arguments explicit. Both restrictions have the ambient value `σ a`, and
  `eInteger` preserves that ambient value by construction.
- `hmem` identifies membership in the supplied maximal ideal `𝓂[L]` with
  membership in `target.maximalIdeal`. It uses
  `IsLocalRing.mem_maximalIdeal` on both sides and
  `map_mem_nonunits_iff eInteger`: a ring equivalence preserves nonunits.

Subgroup extensionality then reduces the lower equality to a membership
equivalence for each `σ : Gal(L/K)`. The published M160 criterion rewrites
residue-kernel membership as the requirement that every supplied-ring
displacement belongs to `𝓂[L]`.
`Higher.mem_lowerRamificationGroup_nat_iff` at natural index `0` rewrites
chosen lower-group membership as the corresponding displacement condition
in `target.maximalIdeal ^ (0 + 1)`. Simplification gives
`target.maximalIdeal`. Surjectivity of `eInteger` and `hmap`, `hmem` prove
both directions.

For the second conjunct, the published
`localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos`
at `0 ≤ 0` reduces upper numbering to the already proved lower equality.
The source-name theorems project the resulting closed conjunction.
There are no new instances or replacement data declarations in this module.

## Published proof dependencies

The principal theorem imports the published target and the following proof
modules by Lean name:

- [Chosen/supplied comparison](../../../LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/ChosenSuppliedComparisonProof.md):
  equality of the actual valuation subrings.
- [Integer-ring restriction evaluation](../../../LocalField/NonarchimedeanLocalField/GaloisIntegerRing/Proofs.md):
  the ambient-field value of the supplied restriction.
- [Residue-kernel characterizations](../../../LocalField/NonarchimedeanLocalField/ResidueGalois/KernelProofs.md):
  the maximal-ideal displacement criterion.
- [Nonpositive local ramification laws](../Core/NonpositiveProof.md):
  upper/lower equality at zero; this module also imports the
  [natural-index membership law](../../HilbertRamification/RealLowerGroups/LowerGroupProof.md).
- [Chosen valuation-ring automorphism laws](../../HilbertRamification/RealLowerGroups/ValuationSubringAutProof.md):
  evaluation of the chosen restriction in `L`.

The statement and all its imported Lean/Markdown pairs are preserved.
The result is limited to the stated Type 0 setting and full supplied
hypotheses. Host inertia equivalences, filtered reciprocity, final finite
reciprocity assembly, universe transport, comparison with the cohomological
route and a Weil system remain separate obligations.

## Original-source correspondence and modifications

The original is Naganori Yamaguchi's *ClassFieldTheory (NYLL)*,
repository `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean).
Worker 1612 read all 113 lines from the registered local snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified whole-file SHA-256 is
`456328b412a0c609dd32b6b884b72ac84abef430d94c635c89f599ca4aa374ef`.

| Original in `RamificationTheory.LocalField` | Original location | Adapted correspondence |
| --- | --- | --- |
| M328.001 `localLowerRamificationGroup_zero_eq_residue_ker` | declaration 30; telescope/conclusion 31–42; proof 43–94 | First conjunct of the principal theorem; identical source-name consequence with `Langlands.NYLL` prefix and all original binders |
| M328.002 `localUpperRamificationGroup_zero_eq_residue_ker` | declaration 97; telescope/conclusion 98–109; proof 110–111 | Second conjunct and second source-name consequence, retaining all original binders |

The principal theorem assembles the published closed conjunction; it is derived
packaging rather than an additional literal source declaration.
The lower proof uses the same displacement/maximal-ideal argument as the
source but compares directly from the chosen ring. It therefore avoids the
source's change to a supplied unique-extension witness and generic
`lowerRamificationGroup_eq_of_valuationSubring_eq` comparison.
The supplied integer-ring evaluation is discharged by its published theorem
instead of the source's `rfl`. The upper proof retains the source's
nonpositive-index reduction. Namespace prefixes, focused published imports,
the local extension witness and explicit universe-0 chosen uniqueness adapt
the source to this Library. M328 has no patch10 edit.

## Provenance, license and authorship

The registered original is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory was
present at this check on 4 November 2026.

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), including inherited notices,
are unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 106 contributed source extraction, target design, dependency analysis
and the direct chosen-ring proof route. Worker 1612 implemented the proof,
checked the full original and published inputs, and wrote this companion
Markdown. Importing published prerequisites does not reuse their authors'
unpublished proof drafts.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The author development build completed with zero errors and warnings.
Inspection identified the principal declaration as a theorem with no universe
parameters and only `propext`, `Classical.choice` and `Quot.sound`.
These development checks are distinct from independent semantic acceptance,
the candidate's exact-target validation and Integrator publication.
