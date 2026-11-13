# Chosen integer-ring uniformizer is irreducible (M133.005)

`Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer_irreducible`
proves the exact target
`Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer_irreducibleStatement K`
for any universe-polymorphic field `K` with the stated valuative relation,
topology and nonarchimedean local-field instance.

The implemented proof applies `Classical.choose_spec` to Mathlib's
`IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. The published
`chosenIntegerRingUniformizer K` is definitionally the corresponding
`Classical.choose`, so its irreducibility is precisely the choice specification.
The canonical DVR instance on the actual integer ring comes from Mathlib via
the target module. The proof imports only the statement module and uses no
other NYLL proof or local helper.

This is the proof of Naganori Yamaguchi's source unit M133.005,
`LocalFieldTheory.chosenIntegerRingUniformizer_irreducible`, lines 56–61 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the source file SHA-256 is
`8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
Worker 212 extracted the proof, prefixed the namespace with `Langlands.NYLL`,
reduced imports to the exact target module, and changed the written theorem
type to the named Prop target. The proof term, universe and ordered argument
telescope are unchanged. No private draft or compatibility patch is reused.

The original copyright and author header is retained verbatim. The source is
Apache-2.0, copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain in `licenses/NYLL/`.
This proof establishes the local-field support target described above.
