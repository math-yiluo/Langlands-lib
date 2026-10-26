# Universe-zero smallness of nonarchimedean local fields: proof

`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small.{u}` proves
exactly the published proposition
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_smallStatement.{u}`.
It has no additional parameters or premises. Its universally quantified carrier
`K : Type u`, field, valuative relation, topology and
`IsNonarchimedeanLocalField K` structure are all those in the imported target.
The conclusion is `Small.{0} K`, meaning representability in `Type 0`.

## Implemented proof

Let `O = 𝒪[K]` be the integer ring of the supplied valuative relation, and
`I = 𝓂[K]` its maximal ideal. Mathlib's local-field instances give a discrete
valuation ring structure on `O` and finiteness of the residue field `O ⧸ I`.
The maximal ideal is finitely generated because this ring is Noetherian.
`Ideal.finite_quotient_pow` consequently gives finiteness of `O ⧸ I ^ n`
for every natural number `n`, including zero.

Map each integer to the sequence of all its residue classes modulo `I ^ n`.
The discrete valuation ring instance supplies `IsHausdorff I O`.
`IsHausdorff.eq_iff_smodEq` then proves injectivity: equality of all quotient
coordinates gives congruence modulo every power, hence equality in `O`.
Each finite quotient is universe-zero small by `Countable.toSmall`, and
`small_Pi` makes their natural-number-indexed product small. Applying
`small_of_injective` proves `Small.{0} O`. This uses countability only for
the individual finite quotients; it asserts no countability of the product
or of the integer ring.

Mathlib's valuation-integer-ring instance makes `K` the fraction field of
`O`. `IsFractionRing.div_surjective` proves that the map
`O × O → K`, `(a, b) ↦ algebraMap O K a / algebraMap O K b`, is surjective.
The product is universe-zero small, so `small_of_surjective` gives the
required `Small.{0} K`.

No auxiliary mathematical definition or statement is introduced. All facts
about the integer ring, its residue field, ideal powers, fraction field and
smallness come from the imported Library target and Mathlib. In particular,
the implementation does not need an additional completeness premise or a
construction of NYLL's `localCompleteDVF`.

## Source and changes

The proof adapts Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Small.lean`,
theorem `LocalFieldTheory.nonarchimedeanLocalField_small`, lines 30–55.
The full file was read and its SHA-256 verified as
`5525b29447cab84c7c263ac5d7807911095bc4790c883b0be0f75fa845e3de27`.
The registered original is in `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable source is
[Small.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Small.lean>).
No current Library `notes/errata` or project `notes/errata` directory was
present at preparation; this is a scoped lookup.

The adapted name is
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small`.
Instead of the source's elementwise theorem signature, the theorem type is
the unchanged published universal statement. The two NYLL source imports
are replaced by that target and Mathlib's countable-smallness and finite
ideal quotient interfaces. The integer ring and maximal ideal are used
directly from Mathlib. Adic separatedness comes from the discrete valuation
ring instance, rather than the source's `localCompleteDVF` adic-completeness
certificate. Finiteness of all quotient powers is supplied explicitly using
`Ideal.finite_quotient_pow`. The sequence injection and fraction-field
surjection preserve the original mathematical argument.

The Lean source preserves the original copyright and authorship and records
Worker 449's changes. It reuses the existing Apache-2.0
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE), whose hashes match the pinned
originals (`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
The selected original file is absent from the root NOTICE source inventory
and all five `ANTHROPIC_FLT_SOURCE.md` inventories in the registered
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No third-party source listed there is copied into this unit. No feasibility
draft or Worker 25 adaptation is reused.

This result establishes smallness only. It constructs no transported field
structures, coherent Artin family, host reciprocity map or Weil system.
