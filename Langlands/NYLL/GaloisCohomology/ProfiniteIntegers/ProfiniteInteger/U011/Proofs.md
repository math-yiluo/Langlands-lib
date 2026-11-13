# NYLL M009.011: index of natural multiplication

`Langlands.NYLL.ClassFormation.zHatMulNat_range_index` proves the published
proposition `Langlands.NYLL.ClassFormation.zHatMulNat_range_indexStatement n hn`.
Its full parameter telescope is explicit `(n : ℕ) (hn : 0 < n)`, in that order.
The positivity parameter is retained even though the proposition definition's
body does not use it. The conclusion is the natural additive-subgroup index
equality `(zHatMulNat n).toAddMonoidHom.range.index = n` on the actual published
NYLL closure model `ZHat : Type 0`.

## Source correspondence and attribution

This proof adapts Naganori Yamaguchi's
`ClassFormation.zHatMulNat_range_index`, source lines 174–189 (signature
175–176), in `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The upstream copyright, Apache-2.0 license and author header are retained.
See `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
Worker 241 prefixes the namespace with `Langlands.NYLL` and gives the theorem
exactly its named published target as its type. During integration, Integrator
replaced the duplicate index calculation with the existing
`Langlands.NYLL.PortInternal.M009U014.zHatMulNat_range_index`. The target unfolds
to that theorem's conclusion. No helper theorem or instance is exported.

## Implemented proof and prerequisites

The proof directly applies
`Langlands.NYLL.PortInternal.M009U014.zHatMulNat_range_index n hn`. This existing
port of M009.011 follows the same source calculation: identify the image of
multiplication with the reduction kernel, use surjectivity of reduction, and
compute the cardinality of `ZMod n`. It has the same explicit positive integer
parameters and conclusion after unfolding the named proposition.

The proof adds no finiteness premise and uses the canonical multiplication map
`x ↦ n • x` and reduction map of the published closure model.

## Actual direct imports and scope

The direct imports are:

- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`
  for the exact proposition and its data;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U014.Proofs`
  for the existing index theorem.

This focused import set replaces the original module-wide imports and earlier
in-file theorem dependencies. The published target, its paired Markdown, and
its dependencies are unchanged. This unit proves only M009.011; it makes no
host class-formation or reciprocity claim.

## Development checks

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation and theorem inspection succeeded without errors or warnings,
with no universe parameters and only `propext`, `Classical.choice`, and
`Quot.sound` among the theorem's axioms. A separate private check assigned
the unapplied constant `@zHatMulNat_range_index` directly to
`∀ (n : ℕ) (hn : 0 < n), zHatMulNat_range_indexStatement n hn`.
These are development checks; independent exact-target validation and
semantic review remain separate requirements.
