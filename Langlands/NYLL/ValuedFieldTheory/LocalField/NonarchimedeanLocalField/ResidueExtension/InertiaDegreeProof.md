# Inertia degree and the canonical residue extension: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.maximalIdeal_inertiaDeg_eq_residue_finrankStatement`
([target](InertiaDegreeStatement.md), NYLL source unit M138.024) by the theorem

```lean
theorem maximalIdeal_inertiaDeg_eq_residue_finrank :
    maximalIdeal_inertiaDeg_eq_residue_finrankStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory`, the adapted source name. Its type
is the target at the same universe `u`. The theorem says: for nonarchimedean local
fields `K` and `L` with `Algebra K L` and a valuation extension
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`,
Mathlib's inertia degree `(𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K]` of the maximal
ideal of `𝒪[L]` over `𝒪[K]` equals `Module.finrank 𝓀[K] 𝓀[L]`, the degree of the
canonical residue-field extension. No finiteness, separability or Galois
hypothesis is involved.

## Proof

The proof is the source proof after an opening `intro`.

1. `intro K L` followed by anonymous introductions of the ten instance binders
   of the target.
2. Mathlib's `Ideal.inertiaDeg_eq_of_isMaximal (𝓂[K]) (𝓂[L])` states
   `q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q)` for maximal ideals `p` of
   `R` and `q` of `S` with `q` lying over `p`. Instance search supplies both
   maximality facts (maximal ideals of the local rings `𝒪[K]`, `𝒪[L]`) and the
   fact that `𝓂[L]` lies over `𝓂[K]` (Mathlib's instance for the integer-ring
   algebra of a valuation extension). Rewriting turns the goal into
   `Module.finrank (𝒪[K] ⧸ 𝓂[K]) (𝒪[L] ⧸ 𝓂[L]) = Module.finrank 𝓀[K] 𝓀[L]`.
3. `rfl` closes this goal: Mathlib's residue field `𝓀[F]` is
   `IsLocalRing.ResidueField 𝒪[F]`, by definition the quotient `𝒪[F] ⧸ 𝓂[F]`,
   and the residue-field algebra `𝓀[K] → 𝓀[L]` induced by the integer-ring
   algebra agrees definitionally with the quotient algebra.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no
errors or warnings. Inspection of the theorem reported kind `theorem`, level
parameters `[u]`, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.InertiaDegreeStatement`:
  the target. Through its imports
  (`Mathlib.RingTheory.RamificationInertia.Inertia` among them) it also supplies
  `Ideal.inertiaDeg_eq_of_isMaximal`.

The published target is imported and used by name; it is not modified.

## Source correspondence and changes

The original theorem is `LocalFieldTheory.maximalIdeal_inertiaDeg_eq_residue_finrank`
at lines 308–319 (docstring at 308, theorem at 311, proof at 318–319) of
Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L308-L319)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`). Its
statement is the published target.

Worker 4699 made these changes on 15 November 2026:

1. Prefix the namespace with `Langlands.NYLL`; keep the theorem name.
2. State the theorem's type as the published closed proposition
   `maximalIdeal_inertiaDeg_eq_residue_finrankStatement.{u}` instead of the
   source binders and conclusion, and introduce the binders with `intro`.
3. Keep the two source proof lines (`rw [...]`, `rfl`) unchanged.
4. Keep the source docstring and add one sentence naming the target.
5. Replace the source imports by the published statement module, and omit the
   source's `noncomputable section`.
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
