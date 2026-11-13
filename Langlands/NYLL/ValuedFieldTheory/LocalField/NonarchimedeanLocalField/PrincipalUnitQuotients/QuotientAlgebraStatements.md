# Successive quotient and ideal algebra targets (M132.040,046,048,053,062–063,068–069,071,086)

These targets state surjectivity of the principal-unit quotient map; its
identity-class and equality tests using the actual embedded successor subgroup;
the congruence interpretation of that subgroup; unary and binary elimination
for the actual maximal-ideal power quotient; the defining submodule membership
and zero-class tests; invertibility of `1+a` at positive depth; and the fact that
a product of two elements of `𝓂^n` lies in `𝓂^(n+1)` when `1 ≤ n`.

All retain the exact arbitrary-field signature with `[ValuativeRel K]` and no
topology or local-field premise. Both induction targets retain implicit `K`,
explicit `n`, implicit Prop-valued `motive`, explicit quotient class(es) and
explicit representative-wise proof `h`; they remain protected. Binary induction
allows arbitrary two-variable motives on two classes. In M132.071 and M132.086,
`n` remains implicit and `hn : 1 ≤ n` remains explicit. M132.071 also retains
explicit integer `a` and its membership proof `ha`; M132.086 instead quantifies
`a b` as elements of the actual ideal subtype. The quotient tests use the
source's exact unit, ideal and subgroup coercions.

All original names in this table have prefix `LocalFieldTheory.` and all
adapted names have prefix `Langlands.NYLL.LocalFieldTheory.`. The line ranges
end at the original conclusion, before the source proof body.

| Unit | Source statement lines | Original suffix | Adapted suffix |
| --- | --- | --- | --- |
| M132.040 | 594–596 | `principalUnitsSuccQuotMk_surjective` | `principalUnitsSuccQuotMk_surjectiveStatement` |
| M132.046 | 655–659 | `principalUnitsSuccQuotMk_eq_one_iff` | `principalUnitsSuccQuotMk_eq_one_iffStatement` |
| M132.048 | 692–696 | `principalUnitsSuccQuotMk_eq_iff_div_mem` | `principalUnitsSuccQuotMk_eq_iff_div_memStatement` |
| M132.053 | 739–744 | `mem_principalUnits_succ_subgroupOf_iff` | `mem_principalUnits_succ_subgroupOf_iffStatement` |
| M132.062 | 818–824 | `MaximalIdealPowSuccQuot.inductionOn` | `MaximalIdealPowSuccQuot.inductionOnStatement` |
| M132.063 | 833–841 | `MaximalIdealPowSuccQuot.inductionOn₂` | `MaximalIdealPowSuccQuot.inductionOn₂Statement` |
| M132.068 | 911–915 | `mem_maximalIdealPowSuccSubmodule_iff` | `mem_maximalIdealPowSuccSubmodule_iffStatement` |
| M132.069 | 919–923 | `maximalIdealPowSuccQuotMk_eq_zero_iff` | `maximalIdealPowSuccQuotMk_eq_zero_iffStatement` |
| M132.071 | 946–948 | `isUnit_one_add_of_mem_maximalIdeal_pow` | `isUnit_one_add_of_mem_maximalIdeal_powStatement` |
| M132.086 | 1161–1164 | `maximalIdealPow_mul_mem_succ` | `maximalIdealPow_mul_mem_succStatement` |

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

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.MaximalIdealDefinitions`

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
