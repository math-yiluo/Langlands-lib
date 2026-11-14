# The local multiplicative group satisfies the class-field axiom: target

This module publishes one closed Prop-valued statement target, the statement
phase of NYLL source row M159.002. It contains no proof. A later
`lean.proof@1` task proves it under the name
`Langlands.NYLL.LocalClassFieldTheory.separableClosureUnits_isClassFormation`.

## Original source

Adapted by Worker 90 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalClassFieldAxiom.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalClassFieldAxiom.lean>)
(SHA-256 `3a15c566db6b1107af9f5184bf4affa73988d7c77399b7cb8660116bebdde9b2`).
The registered source collection is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M159.002 | `LocalClassFieldTheory.separableClosureUnits_isClassFormation`, docstring 144–146, signature 147–151, proof 152 | `Langlands.NYLL.LocalClassFieldTheory.separableClosureUnits_isClassFormationStatement` |

The source proof applies the private theorem M159.001
`galoisAmbientUnits_satisfiesClassFieldAxiom` (lines 35–142), which is not
part of this unit.

## The statement

```lean
def separableClosureUnits_isClassFormationStatement
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Prop :=
  SatisfiesClassFieldAxiom
    (galoisAmbientUnitsRep k (SeparableClosure k))
```

The parameters are those of the source theorem, in its order. `k` lies in
`Type` (universe zero), as in the source. `ValuativeRel k`,
`TopologicalSpace k` and `IsNonarchimedeanLocalField k` are Mathlib's
(`Mathlib.NumberTheory.LocalField.Basic`): `k` is a non-archimedean local
field, its topology coming from its valuation, locally compact and
non-discrete. `SeparableClosure k` is Mathlib's separable closure of `k`
inside `AlgebraicClosure k`.

The conclusion uses the published
`Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep k Ω :=
Rep.ofAlgebraAutOnUnits k Ω`, the actual representation of
`Gal(Ω/k)` on `Ωˣ` written additively, at `Ω = SeparableClosure k`, and
the predicate `Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom` for
the group `Gal(SeparableClosure k / k)` (in `Type 0`) with its Krull
topology. So the target says: for every closed subgroup `K` of finite index
in the absolute Galois group and every finite cyclic subextension `E` of
`K`, the Tate groups of the `E.field`-invariants `(Ω^{E.field})ˣ` under
`Q = K / E.field` satisfy `#Ĥ⁰ = [K : E.field]` and `#Ĥ⁻¹ = 1`, both being
finite.

The three valuation and topology instances are not used to form the
conclusion. They are hypotheses of the source theorem and are kept as
explicit binders: a `def` would otherwise drop them from its telescope.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M072.002, `ClassFormation.SatisfiesClassFieldAxiom` | `Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions` |
| M088.001, `LocalClassFieldTheory.galoisAmbientUnitsRep` | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.Initial.Definitions` |

## Modifications

Worker 90 made these changes to the source theorem:

- The theorem becomes a Prop-valued `def` with the `Statement` suffix
  whose body is the source conclusion; the proof is omitted for the separate
  proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the two Library modules above and the
  Mathlib modules `Mathlib.FieldTheory.IsSepClosed` (`SeparableClosure`),
  `Mathlib.FieldTheory.KrullTopology` (the topology on the Galois group) and
  `Mathlib.NumberTheory.LocalField.Basic` (`IsNonarchimedeanLocalField`).
- The source `noncomputable section` and the `open` lines are omitted,
  except `open ClassFormation`, which names `SatisfiesClassFieldAxiom` as in
  the source. All other declarations of the source file, including the private
  theorem M159.001, are omitted.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The Library's
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) match the pinned upstream
files (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
NYLL's internal class-field axiom does not discharge the host class-formation
targets, and this support unit makes no claim to discharge the host
class-formation, cup, transfer, Tate or reciprocity targets.
