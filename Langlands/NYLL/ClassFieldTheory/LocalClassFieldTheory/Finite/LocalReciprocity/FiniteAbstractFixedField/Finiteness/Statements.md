# Finite abstract fields inside a Galois ambient field: finiteness targets

This module publishes three closed Prop-valued statement targets, the statement
phase of NYLL source rows M099.003, M099.004 and M099.005. It contains no
proofs. Later `lean.proof@1` tasks prove each target under the source theorem
name, in the namespace `Langlands.NYLL.LocalClassFieldTheory`.

## Original source

Adapted by Worker 90 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean>)
(SHA-256 `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`).
The registered source collection is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The source section variables are on line 31:
`variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.003 | `LocalClassFieldTheory.ambientQuotientFiniteOfAbstractFinite`, `omit [IsGalois k Ω] in` on line 48, docstring 49–50, signature 51–55, proof 56–64 | `Langlands.NYLL.LocalClassFieldTheory.ambientQuotientFiniteOfAbstractFiniteStatement` |
| M099.004 | `LocalClassFieldTheory.abstractFiniteClosedSubgroup_isOpen`, `omit [IsGalois k Ω] in` on line 66, docstring 67–68, signature 69–73, proof 74–78 | `Langlands.NYLL.LocalClassFieldTheory.abstractFiniteClosedSubgroup_isOpenStatement` |
| M099.005 | `LocalClassFieldTheory.abstractFixedField_finiteDimensional`, docstring 80–81, signature 82–86, proof 87–90 | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensionalStatement` |

The proof names `Langlands.NYLL.LocalClassFieldTheory.ambientQuotientFiniteOfAbstractFinite`,
`Langlands.NYLL.LocalClassFieldTheory.abstractFiniteClosedSubgroup_isOpen` and
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensional`
are reserved for the later proof tasks.

## The three statements

All three targets share the parameters, in the source order,

```lean
(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
(H : ClosedSubgroup (Gal(Ω/k)))
(hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
  extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H)))
```

and the third adds `[IsGalois k Ω]` after `[Algebra k Ω]`. Both fields lie in
`Type` (universe zero), as in the source. `Gal(Ω/k)` is Mathlib's
`Ω ≃ₐ[k] Ω` with its Krull topology, and `H` is an arbitrary closed subgroup
of it. The hypothesis `hfinite` says that `H`, viewed inside the full group
`(baseField Gal(Ω/k)).toSubgroup = ⊤` through `Subgroup.subgroupOf`, has
finitely many cosets there. This is the finite-over-base condition of the
abstract class-formation presentation.

- `ambientQuotientFiniteOfAbstractFiniteStatement k Ω H hfinite` is
  `Finite (Gal(Ω/k) ⧸ H.toSubgroup)`: the same subgroup has finitely many
  cosets in the ambient group itself.
- `abstractFiniteClosedSubgroup_isOpenStatement k Ω H hfinite` is
  `IsOpen H.carrier`: the subgroup is open in the Krull topology.
- `abstractFixedField_finiteDimensionalStatement k Ω H hfinite` is
  `FiniteDimensional k (abstractFixedField k Ω H)`: the fixed field
  `IntermediateField.fixedField H.toSubgroup` is finite-dimensional over `k`.

The Galois hypothesis is absent from the first two targets because the source
omits it there with `omit [IsGalois k Ω] in`; the third source theorem keeps
the section instance, and so does its target. The hypothesis `hfinite` is not
mentioned in any conclusion; it is a genuine hypothesis of each target, as in
the source.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M010.003, `ClassFormation.baseField` (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, line 50) | `Langlands.NYLL.ClassFormation.baseField`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions` |
| M010.005, `ClassFormation.le_baseField` (same file, line 61) | `Langlands.NYLL.ClassFormation.le_baseField`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| M004.002, `CyclicCohomology.extensionSubgroup` (`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, line 51) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M099.001, `LocalClassFieldTheory.abstractFixedField` (this source file, line 34) | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |

These are used verbatim; in particular the statements apply the published proof
`le_baseField H` inside `extensionSubgroup`, exactly as the source does.

## Modifications

Worker 90 made these changes to the source theorems:

- Each theorem becomes a Prop-valued `def` with the `Statement` suffix whose
  body is the source conclusion. The proofs are omitted for the separate proof
  phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The section variables are written as explicit binders of each definition in
  the source order. For the first two targets they omit `[IsGalois k Ω]`, as
  the source `omit` lines do. For the third they keep it: a `def` drops an
  unused section instance, while the source theorem keeps it, so an explicit
  binder is needed to preserve the source telescope.
- `set_option linter.unusedVariables false in` precedes each definition,
  because the conclusions do not mention `hfinite`. It affects only the linter.
- The source imports are replaced by the three Library modules that provide
  `le_baseField` (which imports `baseField`), `extensionSubgroup` and
  `abstractFixedField`. The source `noncomputable section` and the `open`
  lines are omitted, except `open CyclicCohomology ClassFormation`, which
  names `extensionSubgroup`, `baseField` and `le_baseField` as in the source.
- All other declarations of the source file are omitted; Task 5865 publishes
  them under the sibling `Initial` directory.

## Focused check

A private Lean check, not part of this submission, restates the three source
theorems with the source `variable` line, the source `omit` lines and the
unchanged source proofs, against this module. All three proofs compile in the
project environment, the `#check` telescopes of each source theorem and its
target agree binder for binder, and each source theorem is accepted as a
term of `∀ …, <target> k Ω H hfinite`. This confirms that each target is the
source statement. It is not a submitted proof.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The Library's
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
