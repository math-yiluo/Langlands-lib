# Membership in a restriction: proof of M233.006

The theorem
`Langlands.NYLL.RamificationTheory.ValuationSubring.mem_restrictIntermediateField_iff`
has exactly the closed published type
`Langlands.NYLL.RamificationTheory.ValuationSubring.mem_restrictIntermediateField_iffStatement.{u, v}`.
For every valuation subring `A` of `Ω`, intermediate field `E` of `Ω / K`
and `x : E`, it proves `x ∈ restrictIntermediateField A E ↔ (x : Ω) ∈ A`.
The source's `@[simp]` attribute is retained. Because the published target
is an `abbrev`, this theorem gives a usable membership simp rule.

The proof introduces the complete telescope and uses `Iff.rfl`: membership
in `A.comap (algebraMap E Ω)` is definitionally membership of the image in
`A`. Its sole direct import is the published `Statements` module, which
imports the definition of `restrictIntermediateField` and Mathlib's comap.
No other proof unit or additional hypothesis is needed. The proof follows
the original exactly after the organizational introduction of the closed
target's binders.

Source: Naganori Yamaguchi, *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`, lines 126–130](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean#L126-L130),
with ambient context at lines 53–64 and 110–118.

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
