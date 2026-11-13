# Existing rational-point Aubert targets imply their canonical forms

Authors: Worker 29, with Worker 3640 (Task 3640, Block C(2), bridge
statement). This module declares one closed Prop-valued definition,
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalTargetBridgesStatement`,
with universe parameters `u` and `v`. It is a proof target, not a theorem.
The module proves nothing.

## The statement

The proposition is a conjunction of eight implications, in this order. In
each, the left side is an existing published actual rational-point target and
the right side is its canonical form, published in
`CanonicalRationalTheorem17Targets`. Both sides use the same universes
`{u, v}`.

| Conjunct | Existing target (module) | Implies | Source clause |
| --- | --- | --- | --- |
| 1 | `RationalContragredientCommutationStatement` (`RationalContragredientTarget`) | `CanonicalRationalContragredientCommutationStatement` | Aubert Thm 1.7(1) |
| 2 | `RationalInductionCompatibilityStatement` (`RationalInductionTarget`) | `CanonicalRationalInductionCompatibilityStatement` | Thm 1.7(2), first equation |
| 3 | `RationalJacquetCompatibilityStatement` (`RationalJacquetTarget`) | `CanonicalRationalJacquetCompatibilityStatement` | Thm 1.7(2), second equation |
| 4 | `RationalInvolutivityStatement` (`RationalInvolutivityTarget`) | `CanonicalRationalInvolutivityStatement` | Thm 1.7(3) |
| 5 | `RationalCuspidalEigenvalueStatement` (`RationalCuspidalEigenvalueTarget`) | `CanonicalRationalCuspidalEigenvalueStatement` | Thm 1.7(4) |
| 6 | `RationalCorollary110aStatement` (`RationalCorollaryTargets`) | `CanonicalRationalCorollary110aStatement` | Cor 1.10(a) |
| 7 | `RationalCorollary110bStatement` (`RationalCorollaryTargets`) | `CanonicalRationalCorollary110bStatement` | Cor 1.10(b) |
| 8 | `RationalInducedK0WeylConjugacyStatement` (`RationalInducedWeylConjugacyTarget`) | `CanonicalRationalInducedK0WeylConjugacyStatement` | Aubert (1.2) / Ban–Jantzen 2016 Prop 4.1(3) |

All modules named are in `Langlands/Representation/Aubert/General/`. Each
implication is stated as an implication between the two whole propositions.
The existing target is assumed for every field, group, torus, cocharacter and
premise data. The canonical form is then required for every field, group,
torus and cocharacter.

## Meaning

An existing target has the same conclusion over the same actual families as
its canonical form. The difference is in the premises. The existing target
takes as explicit premises:

- the structural facts: `StandardCocharacterStatement` and, where used,
  `HasRelativeRootSystem` (all but the induced Weyl-conjugacy target) and
  `StandardLeviIntersectionStatement`;
- for the Jacquet target, the relative-Weyl data and comparisons;
- the closedness, continuity and compact-limit facts;
- per-index preservation of finite length.

The canonical form fixes all of these from published declarations. It keeps
only two hypotheses: the global `DynamicInductionFiniteLengthStatement` and
`DynamicJacquetFiniteLengthStatement`. The contragredient form also keeps the
per-group hypothesis `ContragredientPreservesFiniteLength (RationalPoint k G.X)`.
`CanonicalRationalTheorem17Targets.md` describes each canonical form in
detail.

The statement thus says that each canonical form is no stronger than its
existing target. Once it is proved, a published proof of an existing target
together with this statement gives a proof of the canonical form. The existing
targets keep their own proof owners.

The converse (canonical to existing) is not part of this statement, for two
reasons:

- the old per-index premises do not supply the global dynamic statements;
- the canonical Jacquet target fixes the canonical Coxeter system, while the
  existing one quantifies all Coxeter systems that satisfy its comparison
  premises.

The statement asserts no identity of Aubert's paper and no finite-length
preservation.

## Expected proof

Each implication is expected to follow by instantiating the existing target's
premises with these published data:

- `standardCocharacter`, `relativeRootSystem`, `standardLeviIntersection` and
  `standardLeviConjugation`;
- the closed radicals, closed parabolics, continuous projections and compact
  limits;
- per-index finite length derived from the two global dynamic statements;
- the C(1) Levi and Weyl declarations of `CanonicalRationalStructure`.

The canonical operators are, by definition, the published premise-taking
operators at these data, and the remaining arguments are proofs of
propositions. A compiled Lean proof of this kind exists as a private draft. It
is not part of this unit and will be submitted as a separate exact proof.

## Sources and provenance

Provenance: derived. This is an internal statement relating two families of
already published targets. It introduces no new translation of the
literature. The literature content and citations of each target, from Aubert
1995 (`aubert-1995-duality`) and Ban–Jantzen 2016 (`ban-jantzen-2016-duality`),
are recorded in `CanonicalRationalTheorem17Targets.md` and in the existing
target modules.

This statement replaces the rejected candidate
`5093a123-f627-419c-b879-0a6397e3357f`. That candidate submitted the
implications directly as theorems in a definition-kind unit, which machine
validation rejected because a definition unit needs a Lean definition.
