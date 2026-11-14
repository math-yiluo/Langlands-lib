# Abstract reciprocity: the three halves of the class field axiom

This module publishes three closed Prop-valued statement targets, the
statement phase of NYLL source rows M072.003, M072.004 and M072.005. It
contains no proofs. Later `lean.proof@1` tasks prove each target under the
source theorem name in the namespace
`Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom`.

## Original source

Adapted by Worker 90 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean>)
(SHA-256 `5251ee8dafd55cbbf1dc7258b7a0a577b2a2b3c1d9a4f020f4afce8013211814`).
The registered source collection is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The section variables are line 34,
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, and,
inside `namespace SatisfiesClassFieldAxiom` (lines 64–98), line 66,
`variable {A : Rep ℤ G}`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M072.003 | `ClassFormation.SatisfiesClassFieldAxiom.tateHZero_card`, docstring 68–69, signature 70–74, proof 75 | `Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHZero_cardStatement` |
| M072.004 | `ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_card`, docstring 77–78, signature 79–82, proof 83 | `Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_cardStatement` |
| M072.005 | `ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_isZero`, docstring 85–86, signature 87–90, proof 91–96 | `Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_isZeroStatement` |

## The three statements

All three targets have the telescope, in the source order,

```lean
{G : IntegralRepGroupType} [Group G] [TopologicalSpace G] {A : Rep ℤ G}
(hcf : SatisfiesClassFieldAxiom A)
(K : FiniteAbstractField G) (E : FiniteCyclicSubextension K)
```

with `SatisfiesClassFieldAxiom`, `FiniteAbstractField` and
`FiniteCyclicSubextension` as described in the paired definitions module.
Their propositions are

- `tateHZero_cardStatement hcf K E`:
  `Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
  (E.toFiniteAbstractExtension.degree : ℕ)`, i.e. `#Ĥ⁰(G(L/K), A_L) = [L : K]`;
- `tateHMinusOne_cardStatement hcf K E`:
  `Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1`;
- `tateHMinusOne_isZeroStatement hcf K E`:
  `CategoryTheory.Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1))`,
  i.e. the `ℤ`-module `Ĥ⁻¹(G(L/K), A_L)` is a zero object of `ModuleCat ℤ`.

The hypothesis `hcf` is not mentioned in any conclusion; it is a genuine
hypothesis of each target, as in the source. The first two are the
`tateHZero_card` and `tateHMinusOne_card` fields of `hcf K E`; the third
needs in addition the finiteness field, as in the source proof.

## Modifications

Worker 90 made these changes to the source theorems:

- Each theorem becomes a Prop-valued `def` with the `Statement` suffix
  whose body is the source conclusion; the proofs are omitted for the separate
  proof phase.
- The namespace `ClassFormation` is prefixed with `Langlands.NYLL`.
- The source section variables are kept as section variables. Every one of
  them occurs in each target's type (`A` through `hcf`), so each target has
  exactly the source telescope; a focused check confirms this (below).
- `set_option linter.unusedVariables false in` precedes each definition,
  because the conclusions do not mention `hcf`. It affects only the linter.
- The module imports the paired definitions module. The source
  `noncomputable section` is omitted; the `open CyclicCohomology` and
  `open CategoryTheory` lines are kept.

## Focused check

A private Lean check, not part of this submission, restates the three source
theorems with the source section variables and the unchanged source proofs.
All three proofs compile in the project environment, the `#check`
telescopes of each source theorem and its target agree binder for binder, and
each source theorem is accepted as a term of `∀ …, <target> hcf K E`. It is
not a submitted proof.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The Library's
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned upstream
files (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
