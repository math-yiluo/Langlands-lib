# Normalized valuation modulo a degree

`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree` is the additive
homomorphism `Additive Kˣ →+ ZMod n` obtained by composing the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K`
with `Int.castAddHom (ZMod n)`.

Its parameters are an explicit `K : Type u` at arbitrary universe `u`,
instance parameters `[Field K] [ValuativeRel K] [TopologicalSpace K]
`[IsNonarchimedeanLocalField K]`, and an explicit `n : Nat`. There is no
positivity or nonzero hypothesis on `n`; at zero the codomain is `ZMod 0`.
The unit valuation uses the published NYLL convention, without negating it.

## Source and changes

This is M266.001, `LocalClassFieldTheory.valuationModDegree`, at lines 30–34
of `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The full source file was read.
The source file SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is in registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
The related supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable errata entry was found in the project errata notes.

| Source declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.valuationModDegree` | `Langlands.NYLL.LocalClassFieldTheory.valuationModDegree` |

Worker 205 added the namespace prefix and modification record, extracted
this single definition, and replaced the source imports with the published
M134.001–002 `ValuationExactSequence.Definitions` and
`Mathlib.Data.ZMod.Basic`. The universe, telescope, noncomputable status,
result type, and construction body are unchanged. This extraction uses the
published valuation map by Lean name. It needs no theorem from the source
Norm or NormQuotient modules. A focused development check tests this smaller
import set; it does not establish acceptance of later source units.

The original copyright and author header is retained. Apache-2.0 license
and notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No patch10 adaptation or other worker's draft was reused. This unit contains
only the map data; evaluation, surjectivity, and congruence targets are
separate source units.

The focused Lean-service check succeeded with zero errors and zero warnings in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Declaration inspection confirms
an ordinary definition with the single universe parameter `u`, using only
`propext`, `Classical.choice`, and `Quot.sound`.
