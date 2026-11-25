# Actions on the invariants of a Frobenius fixed field

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusFixedFieldAction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a profinite group `G` (compact, Hausdorff, totally disconnected), a `G`-module `A` and a degree map `D`, let `K` be a finite residue abstract field, `L ≤ K` closed with `G_L` normal in `G_K`, `σ` a Frobenius element of `G_K / I_L` and `Σ` its fixed field. A class `q ∈ G_K / I_L` commuting with `σ` normalizes `G_Σ`, so it acts on the invariants `A_Σ`. This file defines that action and shows it is compatible with relative norms between fixed fields, with inclusion into the invariants of the maximal unramified extension `L̃`, and with Frobenius power sums.

## Main definitions and results

- `DegreeData.frobeniusFixedFieldAction`: for `q σ = σ q`, the additive endomorphism of `A_Σ` given by the representative `k = Quotient.out q`, `a ↦ k · a`.
- `frobeniusFixedFieldAction_coe` and `frobeniusFixedFieldAction_coe_of_mk`: the action is `a ↦ k · a` for the chosen representative, and also for any other representative `k` of `q`, since two representatives differ by an element of `I_L ⊆ G_Σ`.
- `frobeniusFixedFieldAction_eq_conjugateStableAction`: the action agrees with the library's general action on a conjugation-stable fixed field.
- `relativeNorm_frobeniusFixedFieldAction`: for two Frobenius elements `σ`, `σ'` with `Σ' ⊇ Σ` finite and `q` commuting with both, the relative norm `A_Σ' → A_Σ` commutes with the action of `q`.
- `frobeniusFixedFieldAction_inclusion`: inclusion `A_Σ → A_L̃` intertwines the action of `q` on `A_Σ` with the quotient action `frobeniusQuotientAction` on `A_L̃`.
- `fixedFieldPowerSum_relativeNorm` and `fixedFieldPowerSum_inclusion`: the sum of the `qⁱ a` for `i < n` commutes with the relative norm, and after inclusion into `A_L̃` becomes the Frobenius power sum `frobeniusPowerSum q n`.

## Proofs

Stability of `G_Σ` under conjugation by the representative of `q` comes from the preceding file on Frobenius-closure commutation; norm compatibility then follows from the general result that relative norms commute with conjugation-stable actions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldAction.lean`: the Lean file is the source byte for byte (SHA-256 `6be37ea532b27ce06e6ebac584c0442879ad599f28e3028ff4de11a675a0e72e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
