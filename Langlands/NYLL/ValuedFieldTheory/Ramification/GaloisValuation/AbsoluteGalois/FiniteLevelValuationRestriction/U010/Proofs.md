# Automorphic translates preserve extension: proof of M233.010

The theorem `Langlands.NYLL.RamificationTheory.ValuationSubring.smul_hasExtension`
has exactly the closed published type
`Langlands.NYLL.RamificationTheory.ValuationSubring.smul_hasExtensionStatement.{u, v, w}`.
For an arbitrary valuation `v` of `K`, a valuation subring `A` of `Ω` whose
canonical valuation extends `v`, and a `K`-algebra automorphism `σ` of `Ω`,
it proves that the canonical valuation of `σ • A` also extends `v`.
The pointwise scope is opened locally, as in the source, and all three
universes and all instance hypotheses are preserved.

The proof follows the source. It uses
`Valuation.HasExtension.ofComapInteger` and extensionality to compare
subrings of `K`. The integer ring of the translated subring's canonical
valuation is the translated subring. The pointwise membership rule turns
membership in `σ • A` into membership of the inverse image under `σ` in
`A`. Since `σ⁻¹` is a `K`-algebra automorphism, `(σ⁻¹).commutes x` fixes the
image of every `x : K`. The required membership equivalence is then the
given extension's `Valuation.HasExtension.val_map_le_one_iff`, after
rewriting with the canonical valuation's `valuation_le_one_iff`.

The sole direct import is the published `Statements` module; its imports
provide the pointwise action and the Mathlib valuation-extension API.
This proof does not depend on the other M233 proof units. The mathematical
steps are unchanged from the source; only the closed target introductions,
qualified Mathlib names, `Langlands.NYLL` namespace and focused import are
adapted.

Source: Naganori Yamaguchi, *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`, lines 170–190](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean#L170-L190),
with ambient context at lines 53–64 and 110–118 and Pointwise scope at line 150.

Worker 256 read the entire 344-line upstream source. The source file SHA-256
is `bc2b582cac15fc4a9c6dc94e9687368e2a1bf91ca9d4111d41a9458fe8e49889`.
The registered originals are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No matching source erratum was found. The original copyright and author
header are preserved; Apache-2.0 applies. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
The Lean header records the modifications by Worker 256 on 13 November 2026.
Worker 122 supplied the compiled closed-target proof guidance and is credited
as a coauthor. The published statement and all published imports are unchanged.
All checks use approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
These are valuation-subring support results, with no assertion about host
reciprocity or class formation.
