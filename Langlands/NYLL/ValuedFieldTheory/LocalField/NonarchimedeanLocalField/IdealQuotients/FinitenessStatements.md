# Finiteness target for successive principal-unit quotients (M133.058)

This module extracts the exact statement from Naganori Yamaguchi's
NYLL ClassFieldTheory,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean),
pinned at `fbd320cd8b1b06487c58227e92eb135794267709`. The original file
SHA-256 is `8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
The registered readable snapshot is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata directory.

## Exact source correspondence

Source unit M133.058 is the theorem
`LocalFieldTheory.finite_principalUnitsSuccQuot`, lines 907–910
(the full declaration and proposition, before its proof).
The adapted Prop-valued definition is
`Langlands.NYLL.LocalFieldTheory.finite_principalUnitsSuccQuotStatement`.
Both retain the arbitrary universe `u` and this complete ordered telescope:

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n)
```

The body is exactly `Finite (PrincipalUnitsSuccQuot K n)`.
The explicit hypothesis `hn` remains an argument even though the body does
not mention it. This target asserts finiteness of the actual quotient
`U^n/U^(n+1)` for the supplied valuation and `n ≥ 1`. It neither assumes
finiteness of that quotient nor asserts a cardinality formula.

The dependency is source M132.001,
`LocalFieldTheory.PrincipalUnitsSuccQuot`, from
`PrincipalUnitQuotients.lean:28–30`. The published
`Langlands.NYLL.LocalFieldTheory.PrincipalUnitsSuccQuot` is imported from
`PrincipalUnitQuotients.SuccessorDefinitions`. That definition is the quotient
of `principalUnits K n` by the subgroup induced by
`principalUnits K (n + 1)`, with no topology or local-field hypothesis.
This module reuses that actual quotient by Lean name.

## Modification record

Worker 201 changed the source theorem command to a Prop-valued definition,
added the `Statement` suffix and the `Langlands.NYLL` namespace prefix,
and omitted the proof at lines 911–912. The source universe, binder kinds,
order, hypotheses and proposition are unchanged. The original theorem
docstring was replaced by a source-unit label. The source noncomputable
section and unused `ValuativeRel` notation scope are omitted.

The module replaces the broad source imports with Mathlib's local-field class
from `Mathlib.NumberTheory.LocalField.Basic` and the published quotient from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions`.
These imports supply the objects and class used in this proposition.

No theorem proof, new axiom, helper, original-namespace alias or instance
is included. In particular the source proof's residue-field equivalence
is not needed to state this target.

## Attribution and scope

The source copyright/author header is retained verbatim: copyright 2026
Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../licenses/NYLL/LICENSE), SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and [NOTICE](../../../../../../licenses/NYLL/NOTICE), SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
are retained in the Library. These relative links use the eventual public
module location.

This file supplies a statement target only. Its proof belongs to separate
work. It discharges no host class-formation, cup, transfer, Tate or
reciprocity claim.
