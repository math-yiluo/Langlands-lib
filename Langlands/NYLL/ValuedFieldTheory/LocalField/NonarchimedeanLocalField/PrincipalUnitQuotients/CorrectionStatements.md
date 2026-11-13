# Correction-product tail control and convergence targets (M132.022–032,076)

These targets concern the actual recursive product `principalUnitsCorrectionProduct`.
They state its successor equation, membership in the initial principal-unit
level, multiplicative and additive control of tails, the unit subtraction
identity, control for any two late indices, its Cauchy property, existence of an
integer-ring limit, retention of the congruence by any limit, existence with
that congruence, and existence of a limit represented by an actual principal unit.

The algebraic targets use only `(K : Type u) [Field K] [ValuativeRel K]`.
The uniform and limit targets M132.029–032,076 retain in source order
`[UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]`.
Every correction sequence has its dependent source type
`∀ d : Nat, principalUnits K (n + d)`. Source orders of natural indices and
sequence arguments are unchanged, including `(n d : Nat)` before `z` in
M132.022, `(n m d : Nat)` before `z` in tail targets, and `(n N i j : Nat)`
followed by `z`, `hi`, `hj` in M132.028. M132.031 keeps explicit `x` and `hx`.
M132.076 alone includes explicit `hn : 1 ≤ n` after explicit `n`; its limit
is quantified in `principalUnits K n` and viewed in the integer ring by both
source coercions. No positivity premise is inserted in the preceding targets.

All original names in this table have prefix `LocalFieldTheory.` and all
adapted names have prefix `Langlands.NYLL.LocalFieldTheory.`. The line ranges
end at the original conclusion, before the source proof body.

| Unit | Source statement lines | Original suffix | Adapted suffix |
| --- | --- | --- | --- |
| M132.022 | 323–327 | `principalUnitsCorrectionProduct_succ` | `principalUnitsCorrectionProduct_succStatement` |
| M132.023 | 332–335 | `principalUnitsCorrectionProduct_mem` | `principalUnitsCorrectionProduct_memStatement` |
| M132.024 | 347–352 | `principalUnitsCorrectionProduct_div_mem` | `principalUnitsCorrectionProduct_div_memStatement` |
| M132.025 | 382–387 | `principalUnitsCorrectionProduct_div_sub_one_mem` | `principalUnitsCorrectionProduct_div_sub_one_memStatement` |
| M132.026 | 396–399 | `unit_sub_eq_mul_div_sub_one` | `unit_sub_eq_mul_div_sub_oneStatement` |
| M132.027 | 411–416 | `principalUnitsCorrectionProduct_sub_mem` | `principalUnitsCorrectionProduct_sub_memStatement` |
| M132.028 | 427–433 | `principalUnitsCorrectionProduct_sub_mem_of_le` | `principalUnitsCorrectionProduct_sub_mem_of_leStatement` |
| M132.029 | 457–462 | `principalUnitsCorrectionProduct_cauchySeq` | `principalUnitsCorrectionProduct_cauchySeqStatement` |
| M132.030 | 479–485 | `exists_tendsto_principalUnitsCorrectionProduct` | `exists_tendsto_principalUnitsCorrectionProductStatement` |
| M132.031 | 491–498 | `principalUnitsCorrectionProduct_limit_sub_one_mem` | `principalUnitsCorrectionProduct_limit_sub_one_memStatement` |
| M132.032 | 512–519 | `exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem` | `exists_tendsto_principalUnitsCorrectionProduct_sub_one_memStatement` |
| M132.076 | 994–1000 | `exists_tendsto_principalUnitsCorrectionProduct_principalUnit` | `exists_tendsto_principalUnitsCorrectionProduct_principalUnitStatement` |

Each original theorem or lemma becomes a `def` returning `Prop`; its original
conclusion is the definition body. Every source hypothesis, universe, parameter,
instance, binder kind and binder order is retained. In particular, an explicit
proof premise remains an explicit parameter even when unused in the conclusion.
Protected declarations remain protected. Source proof bodies and `[simp]` theorem
attributes are omitted. No theorem is proved and no axiom or instance is added.
The source namespace is prefixed by `Langlands.NYLL`; target names receive only
the suffix `Statement`. Source notation scope, universe `u`, noncomputable section
and `open Filter` are retained. Module documentation is restricted to this unit.

The only imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.CorrectionDefinitions`
- `Mathlib.NumberTheory.LocalField.Basic`

These replace the broad source module imports with the precise published data
and Mathlib constructions appearing in the statements. There are no other
mathematical changes. Generic Mathlib quotient and ideal operations are reused,
while these declarations retain the exact NYLL expressions and telescopes.
This support unit discharges no host reciprocity, class-formation or Tate target.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`.
The complete source file SHA-256 is
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata notes.

The original copyright, Apache-2.0 license and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 211 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.
