# Computation target for the unramified norm quotient equivalence

`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormQuotientEquivZMod_mkStatement`
is the closed proposition for source M266.021, theorem
`LocalClassFieldTheory.unramifiedNormQuotientEquivZMod_mk`, lines 214–223.
For every `K : Type u` with `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, every natural `n`
(including zero) and every `x : Kˣ`, it states that the named equivalence
`unramifiedNormQuotientEquivZMod K n` sends `QuotientGroup.mk x` to
`valuationModDegreeMulHom K n x`.

This target uses the M266.020 definition, with its actual valuation subgroup
and published surjectivity and kernel-equality proofs. Worker 205 closed
the source telescope under universal quantifiers and added the `Statement`
suffix. The proposition retains the source's universe, parameters,
hypotheses and equation; the source theorem proof and simp attribute are
reserved for the separate proof unit. This file asserts a target, not its
proof.

## Source correspondence and modifications

The pinned original is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Its full-file SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The complete original file was read, with no applicable errata found.
Worker 205 retained its copyright, author and Apache-2.0 header, added the
modification record and namespace prefix, and used focused imports of the
existing adapted declarations. The license and notices are published at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No other worker's
unpublished draft was reused.

## Development validation

Focused `lean_check` record `10f3cfd6-f298-4890-8dd3-102934064423` at
Library base `410c79471b79f65a02fb0f6070da7f2800793ff3` compiled this module
and inspected the exact declaration with `statement_returns_prop: true`,
universe parameter `u`, zero errors and warnings, and only the standard
`propext`, `Classical.choice` and `Quot.sound` assumptions. This check
is development evidence; it supplies no independent proof acceptance.
