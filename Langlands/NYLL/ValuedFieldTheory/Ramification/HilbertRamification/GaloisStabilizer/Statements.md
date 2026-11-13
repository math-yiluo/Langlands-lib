# Finite-Galois stabilizer criterion: Prop target

This module defines exactly
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.adjoin_le_adjoin_of_forall_fixed_imp_fixedStatement`.
It states the criterion from NYLL unit M396.001; it supplies no proof.

## Pinned source and attribution

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/GaloisStabilizer.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/GaloisStabilizer.lean>).
Its SHA-256 is
`e03c8bdaf43ac682a960ec61815b150bfd116f3b7975777dbf873a282f31471d`.
The theorem declaration and statement occupy **lines 34–39**; the independent
universes, namespace and section parameters occur at lines 24–30. The proof at
lines 40–49 is outside this statement extraction.

The source is registered under
`external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original copyright, Apache-2.0 and author header is retained verbatim.
The repository retains [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE), with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

## Lean meaning and source correspondence

The definition retains `{K : Type u}` and `{M : Type v}` with independent
universes, `[Field K]`, `[Field M]`, the supplied `[Algebra K M]`,
`[FiniteDimensional K M]` and `[IsGalois K M]` as explicit declaration binders.
Its value in `Prop` is

```lean
∀ (a b : M), (∀ σ : Gal(M / K), σ b = b → σ a = a) → K⟮a⟯ ≤ K⟮b⟯
```

Thus the source's `(a b : M)` are universally quantified in the body, and its
`hfixed` is the antecedent of the implication. It requires each actual
`K`-algebra automorphism of `M` that fixes `b` to fix `a`. The conclusion is
containment of the two simple intermediate fields in `M` over the same supplied
algebra. The finite-dimensional and Galois assumptions are retained explicitly
even though forming this proposition does not itself require them.

The reused Mathlib declarations are `Field`, `Algebra`, `FiniteDimensional`,
`IsGalois`, `AlgEquiv` (the automorphisms denoted by `Gal(M / K)`),
`IntermediateField`, and `IntermediateField.adjoin`. Opening the
`IntermediateField` notation scope makes `K⟮a⟯` denote
`IntermediateField.adjoin K {a}`, and `≤` is the canonical containment order
on intermediate fields. Equality and implication have their ordinary Lean
meanings. No new algebra, field, order or Galois instance is introduced.

## Adaptation and scope

Worker 328 prefixed the source namespace
`RamificationTheory.HilbertRamification.Higher` with `Langlands.NYLL`, replaced
the theorem by a Prop-valued `def` with the suffix `Statement`, and moved the
element and stabilizer hypotheses into its body. The source section parameters
are written directly on the definition so that all hypotheses remain in its
type. Both source imports are retained:
`Mathlib.FieldTheory.Galois.Basic` and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`. The source's
`noncomputable section` is unnecessary for this proposition and is omitted.
These are all adaptations; no patch10 edit applies to M396.

The module is Mathlib-only and imports no NYLL module. The original proof uses
fixed-field correspondence, but this module neither ports that proof nor
asserts its theorem. It introduces only the specified target.
