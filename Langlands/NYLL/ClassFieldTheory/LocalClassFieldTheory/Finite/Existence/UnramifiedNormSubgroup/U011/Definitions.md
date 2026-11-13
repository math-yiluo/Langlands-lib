# Valuation-divisibility subgroup

`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup K n` is the
subgroup of `Kˣ` consisting of the units `x` for which `(n : Int)` divides
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
(Additive.ofMul x)`. Its parameters are an explicit `K : Type u` at arbitrary
universe `u`, instance parameters `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, and an explicit natural
number `n`, which may be zero. This construction only uses divisibility of
the published normalized valuation. An equality with the norm subgroup of a
field extension is a separate later theorem.

The three proof fields use the additive homomorphism laws. The identity
has valuation zero; divisibility is closed under addition and negation,
which correspond to multiplication and inversion in `Kˣ`.

## Source and changes

This is M266.011, `LocalClassFieldTheory.unramifiedNormSubgroup`, at source
lines 119–140 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The entire source file was read;
its SHA-256 is `ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the relative source path is `n-yamaguchi-0729--ClassFieldTheory/source/`
followed by the path above. The supplement registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in project errata notes.

| Source declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.unramifiedNormSubgroup` | `Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup` |

Worker 205 extracted this single definition, added the namespace prefix
and modification record, and replaced the source imports with the published
M134.001–002 module `ValuationExactSequence.Definitions`. The original
universe, complete telescope, subgroup carrier, and three proof fields are
unchanged. The focused check tests the reduced dependency set; none of the
preceding ten source commands or the source Norm and NormQuotient modules
is needed to construct this subgroup. The original `noncomputable section`
is retained; no instance is added.

The original 2026 copyright and author header is retained verbatim. Apache-2.0
license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. No patch10 adaptation or other worker's draft was used.

The focused Lean-service check passed with zero errors and zero warnings in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection confirms an ordinary
definition with universe parameter `u` and only `propext`, `Classical.choice`,
and `Quot.sound` among its axioms.
