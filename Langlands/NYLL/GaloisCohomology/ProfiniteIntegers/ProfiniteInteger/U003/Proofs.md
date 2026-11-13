# NYLL M009.003: evaluation of natural multiplication

`Langlands.NYLL.ClassFormation.zHatMulNat_apply` proves exactly the published
proposition `Langlands.NYLL.ClassFormation.zHatMulNat_applyStatement n x`.
The parameters are explicit `n : ℕ` followed by explicit `x : ZHat`.
The proposition is `zHatMulNat n x = n • x`, with no positivity premise;
it includes `n = 0`.

The sole direct import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`.
That module imports the published multiplication data in
`ProfiniteInteger.U002.Definitions` and `Mathlib.GroupTheory.Index`.
The data module in turn imports `ProfiniteIntegerCore.Definitions`, which
supplies the actual Type-zero NYLL closure model `ZHat` and its structures.
The proof uses the existing map and model.

The implementation is `rfl`: unfolding the target and the bundled map's
application exposes its defining field `toFun := fun x => n • x`, so both
sides are definitionally equal. There are no helper declarations and no
prerequisite theorem proofs.

This is adapted from Naganori Yamaguchi's
`ClassFormation.zHatMulNat_apply`, source unit M009.003, lines 58–62
(signature at lines 60–61) of
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The source file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source proof is also `rfl`. Its supporting definition
`ClassFormation.zHatMulNat`, lines 51–56, corresponds to the published
`Langlands.NYLL.ClassFormation.zHatMulNat` in the imported U002 module.

Worker 238 extracts this single theorem, prefixes the namespace with
`Langlands.NYLL`, replaces the source imports with the published statement
module, and writes the conclusion as the named target applied to the same
parameters. The source theorem name suffix, explicit binder order,
`@[simp]` attribute, noncomputable section and proof term are retained.
The target's Lean/Markdown pair and its imports are unchanged.

The original copyright and author header is retained. The Apache-2.0 license
and notices remain in `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
