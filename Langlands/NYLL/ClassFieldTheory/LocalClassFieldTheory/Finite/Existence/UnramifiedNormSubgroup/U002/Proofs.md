# Evaluation of the normalized valuation modulo a degree

`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree_apply` proves exactly
the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree_applyStatement`.
Its sole import is the published `UnramifiedNormSubgroup.AdditiveStatements`
module. The theorem retains the arbitrary universe `u`, every field,
valuation and topology instance, and every natural degree `n`, including zero.
For each `x : Additive Kˣ`, it identifies `valuationModDegree K n x` with the
cast to `ZMod n` of the published normalized integer valuation
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x`.

The proof introduces the target's universally quantified parameters and applies
`rfl`. The published reduced valuation is
`(Int.castAddHom (ZMod n)).comp (valuationMap K)`, whose evaluation reduces
definitionally to that integer cast. This is the original proof route and
requires no valuation-surjectivity result. The theorem carries the original
`simp` attribute.

## Source correspondence and modifications

This is M266.002, source theorem
`LocalClassFieldTheory.valuationModDegree_apply`, lines 37–41 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The original header and source lines 1–85 were read, and the full source file's
SHA-256 was verified as
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable project errata entry was found.

Worker 526 extracted this theorem, added the `Langlands.NYLL` namespace prefix
and modification record, replaced the source imports with the published target
module, and annotated the theorem with that exact closed proposition. The
introduced telescope accounts for this closed target; the equality, hypotheses,
parameter order, universe and `rfl` proof retain their source meanings.
The published statement and its imported definitions are unchanged.
No compatibility patch or other worker's unpublished draft was reused.

The original 2026 Naganori Yamaguchi copyright, Apache-2.0 release and author
header, including “assisted by OpenAI Codex”, are retained verbatim.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

## Development validation

The focused Lean-service build and declaration inspection succeeded in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with zero errors and warnings.
Inspection reports a theorem with universe parameter `u` and only the standard
`propext`, `Classical.choice` and `Quot.sound` assumptions. Independent semantic
review and the submission's exact-target validation are separate requirements.
