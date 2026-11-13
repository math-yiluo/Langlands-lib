# Maximal-ideal powers and local topology targets (M132.012–017)

The first four targets say that every zero-neighborhood in the valuation
integer ring contains a sufficiently deep maximal-ideal power, that all deeper
powers also lie there, and that every power is closed and a zero-neighborhood.
The last two targets give convergence to zero for `x^(d+1)` and `(-x)^(d+1)`
when `x` lies in the maximal ideal. All six keep the explicit `K : Type u`,
`[Field K] [ValuativeRel K] [TopologicalSpace K]` and the actual Mathlib
`[IsNonarchimedeanLocalField K]`. The convergence targets retain implicit `x`
and explicit membership proof `hx`. The ring topology is the canonical subtype
topology on `𝒪[K]`. No discrete or complete structure is supplied by a new axiom;
the same local-field class as in the source is used.

All original names in this table have prefix `LocalFieldTheory.` and all
adapted names have prefix `Langlands.NYLL.LocalFieldTheory.`. The line ranges
end at the original conclusion, before the source proof body.

| Unit | Source statement lines | Original suffix | Adapted suffix |
| --- | --- | --- | --- |
| M132.012 | 162–166 | `exists_maximalIdeal_pow_subset_nhds_zero` | `exists_maximalIdeal_pow_subset_nhds_zeroStatement` |
| M132.013 | 189–194 | `eventually_maximalIdeal_pow_subset_nhds_zero` | `eventually_maximalIdeal_pow_subset_nhds_zeroStatement` |
| M132.014 | 200–203 | `isClosed_maximalIdeal_pow` | `isClosed_maximalIdeal_powStatement` |
| M132.015 | 222–225 | `maximalIdeal_pow_mem_nhds_zero` | `maximalIdeal_pow_mem_nhds_zeroStatement` |
| M132.016 | 247–251 | `tendsto_pow_succ_of_mem_maximalIdeal` | `tendsto_pow_succ_of_mem_maximalIdealStatement` |
| M132.017 | 260–264 | `tendsto_neg_pow_succ_of_mem_maximalIdeal` | `tendsto_neg_pow_succ_of_mem_maximalIdealStatement` |

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
