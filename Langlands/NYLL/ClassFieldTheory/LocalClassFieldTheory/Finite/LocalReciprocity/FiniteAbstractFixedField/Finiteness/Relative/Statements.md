# Finite abstract fields inside a Galois ambient field: relative finiteness target

This module publishes one closed Prop-valued statement target, the statement
phase of NYLL source row M099.018. It contains no proof. A later
`lean.proof@1` task proves it under the source theorem name
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_relativeFiniteDimensional`.

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
The source theorem has no `omit`, so it keeps all five.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.018 | `LocalClassFieldTheory.abstractFixedField_relativeFiniteDimensional`, docstring 304–305, signature 306–317, proof 317–335 | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_relativeFiniteDimensionalStatement` |

## The statement

The target has the parameters, in the source order,

```lean
(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
(K L : ClosedSubgroup (Gal(Ω/k)))
(hLK : L.toSubgroup ≤ K.toSubgroup)
(hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
  extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
(hLKfinite : Finite
  (K.toSubgroup ⧸ extensionSubgroup K L hLK))
```

and its proposition is the source conclusion, unchanged:

```lean
letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
  RingHom.toAlgebra
    (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
FiniteDimensional (abstractFixedField k Ω K)
  (abstractFixedField k Ω L)
```

Both fields lie in `Type` (universe zero), as in the source. `Gal(Ω/k)` is
Mathlib's `Ω ≃ₐ[k] Ω` with its Krull topology; `K` and `L` are closed
subgroups with `L ≤ K`. The hypothesis `hKfinite` says that `K` has finitely
many cosets in the full group `(baseField Gal(Ω/k)).toSubgroup = ⊤`, seen
through `Subgroup.subgroupOf`; `hLKfinite` says that `L` has finitely many
cosets in `K`. So `L / K / k` is a tower of abstract fields, each finite over
the one below.

`abstractFixedField k Ω H` is `IntermediateField.fixedField H.toSubgroup`.
Since `L ≤ K`, the fixed field of `K` is contained in the fixed field of `L`;
this is the published theorem `abstractFixedField_le k Ω hLK` (M099.006).
The conclusion makes the fixed field of `L` an algebra over the fixed field
of `K` through this inclusion, and says that it is finite-dimensional as a
vector space over it: the concrete upper field is a finite extension of the
concrete lower field.

The hypotheses `hKfinite` and `hLKfinite` are not mentioned in the
conclusion. They are hypotheses of the source theorem and are kept.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| M099.006, `LocalClassFieldTheory.abstractFixedField_le` (a proof) | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_le`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U006.Proofs`; its type is `abstractFixedField_leStatement k Ω hLK`, which unfolds to the source type `abstractFixedField k Ω K ≤ abstractFixedField k Ω L` |
| `ClassFormation.baseField`, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`) and the proof `Langlands.NYLL.ClassFormation.le_baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`, which imports the former) |
| `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |

`IntermediateField.inclusion`, `RingHom.toAlgebra` and `FiniteDimensional`
are Mathlib's. No new instance is declared: the `letI` algebra structure is
local to the proposition, as in the source.

## Modifications

Worker 90 made these changes to the source theorem:

- The theorem becomes a Prop-valued `def` with the `Statement` suffix whose
  body is the source conclusion, including its `letI` binder; the proof is
  omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source section variables are written as explicit binders of the
  definition, in the source order. A `def` would otherwise drop the unused
  instance `[IsGalois k Ω]`, which the source theorem keeps.
- The source imports are replaced by the published modules in the table
  above.
- The source `noncomputable section` and the unused opens of
  `RamificationTheory` and `KummerTheory` (line 23) are omitted; the opens of
  `CyclicCohomology` (line 23) and `ClassFormation` (line 25) are kept, as
  the single line `open CyclicCohomology ClassFormation`.
- `set_option linter.unusedVariables false in` precedes the definition,
  because the conclusion does not mention `hKfinite` and `hLKfinite`. It
  affects only the linter.
- The docstring states that it is the M099.018 target and why
  `IsGalois k Ω` is kept.

The module lies in its own `Relative` subdirectory of `Finiteness`, so that
the published `Finiteness/Statements` module (M099.003–M099.005), which has
its own proof tasks, is not changed.

## Focused check

A private Lean check, not part of this submission, restates the source
theorem against this target and compiles its unchanged source proof, taking
the two still unpublished proofs it uses (M040.024
`FiniteGaloisSubextension.finite_extension_trans` and M099.005
`abstractFixedField_finiteDimensional`) as hypotheses in the form of their
published statements. It also checks that the source conclusion is accepted
as a term of the target. It is not a submitted proof.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The Library's
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
