# The additive value of the chosen uniformizer (M133.018)

`Langlands.NYLL.LocalFieldTheory.v_integerRingUniformizerFieldUnit`
proves the exact published proposition
`Langlands.NYLL.LocalFieldTheory.v_integerRingUniformizerFieldUnitStatement K`.
It retains arbitrary `K : Type u` and the source instances `[Field K]`,
`[ValuativeRel K]`, `[TopologicalSpace K]` and `[IsNonarchimedeanLocalField K]`.
Its conclusion is that the NYLL normalized additive valuation of
`Additive.ofMul (integerRingUniformizerFieldUnit K)` is `-1`.

The proof first exposes the conclusion with `change` and applies the
published M133.015 theorem `v_integerRingIrreducibleFieldUnit`. Its arguments are the chosen integer-ring
uniformizer, its published irreducibility proof, the corresponding field unit,
and `rfl` for the equality of underlying field elements. Thus the implemented
proof follows the source proof directly, using its existing normalization
theorem. It imports only the published `UniformizerPowMap.Definitions` target
module and `IdealQuotients.U015.Proofs`; no private helper is needed.

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
`LocalFieldTheory.v_integerRingUniformizerFieldUnit`, M133.018,
lines 265–272 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source file SHA-256 is
`8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
It is readable below
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Worker 642 extracted the proof on 16 November 2026, added the
`Langlands.NYLL` namespace prefix, replaced whole-source imports with the two
published modules above, wrote the theorem type as the exact named Prop target,
and added the initial `change`. The mathematical proof and source sign
convention are preserved. No published statement or imported file is modified.
The original copyright, Apache-2.0 license and author header are retained
verbatim in the Lean file. The original `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This proof establishes the specified local-field support proposition.
