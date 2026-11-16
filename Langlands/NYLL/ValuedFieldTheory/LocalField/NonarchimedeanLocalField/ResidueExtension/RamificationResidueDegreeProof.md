# Ramification index times the canonical residue degree: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement`
([target](RamificationResidueDegreeStatement.md), NYLL source unit M138.029) by the
theorem

```lean
theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank :
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory`, the adapted source name. Its type
is the target at the same universe `u`. The theorem says: for a finite extension
`L/K` of nonarchimedean local fields with a valuation extension, whose integer
ring `𝒪[L]` is a finite `𝒪[K]`-module, the ramification index
`Ideal.ramificationIdx' 𝓂[K] 𝓂[L]` times the residue degree
`Module.finrank 𝓀[K] 𝓀[L]` equals `Module.finrank K L`.

## Proof

The proof is the source proof after an opening `intro`. It combines two Library
proofs, each of whose type is a closed proposition `∀ (K L : Type u) [..], ..`;
applied to `K` and `L`, their instance arguments are found by instance search
among the introduced binders.

1. `intro K L` followed by anonymous introductions of the twelve instance
   binders of the target.
2. `maximalIdeal_inertiaDeg_eq_residue_finrank K L` (M138.024,
   [proof](InertiaDegreeProof.md)) gives
   `(𝓂[L]).inertiaDeg 𝒪[K] = Module.finrank 𝓀[K] 𝓀[L]`. It needs ten of the
   twelve instance binders, omitting `FiniteDimensional K L` and
   `Module.Finite 𝒪[K] 𝒪[L]`. Rewriting right to left replaces the residue
   degree in the goal by the inertia degree.
3. The goal is now exactly the conclusion of
   `maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K L` (M138.028,
   [proof](RamificationInertiaDegreeProof.md)), which closes it with `exact`.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module, together
with the two proof modules it imports, with no errors or warnings. Inspection of
the theorem reported kind `theorem`, level parameters `[u]`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.InertiaDegreeProof`:
  the M138.024 proof `maximalIdeal_inertiaDeg_eq_residue_finrank`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationInertiaDegreeProof`:
  the M138.028 proof `maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationResidueDegreeStatement`:
  the target.

The two proofs are separate focused contributions of the same task and are
imported by Lean name; this module does not copy them. The published target is
imported and used by name; it is not modified.

## Source correspondence and changes

The original theorem is
`LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank` at
lines 382–395 (docstring at 382, theorem at 384, proof at 394–395) of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L382-L395)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`). Its
statement is the published target. The source proof uses the source theorems at
lines 311 (M138.024) and 358 (M138.028), whose adapted names are the two Library
proofs above.

Worker 4699 made these changes on 15 November 2026:

1. Prefix the namespace with `Langlands.NYLL`; keep the theorem name.
2. State the theorem's type as the published closed proposition
   `maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement.{u}`
   instead of the source binders and conclusion, and introduce the binders with
   `intro`.
3. Keep the two source proof lines unchanged; their references now resolve to
   the adapted Library proofs.
4. Keep the source docstring and add one sentence naming the target.
5. Replace the source imports by the published statement module and the two
   proof modules above, and omit the source's `noncomputable section`.
6. Keep the original copyright and author header verbatim and add the
   modification record.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library.
