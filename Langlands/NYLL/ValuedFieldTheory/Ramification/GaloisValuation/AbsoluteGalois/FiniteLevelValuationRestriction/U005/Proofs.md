# Restriction is a comap: proof of M233.005

The theorem
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField_eq_comap`
has exactly the published closed type
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField_eq_comapStatement.{u, v}`.
It says that restricting a valuation subring `A` of `Ω` to an intermediate
field `E` of `Ω / K` is `A.comap (algebraMap E Ω)`, with independent field
universes. The source's `@[simp]` attribute is retained; the published target
is an `abbrev`, so this theorem registers the displayed equality as a usable
simp rule.

The proof introduces the complete telescope and uses `rfl`. Both sides are
the same valuation subring by the published definition
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField`.
The sole direct import is the published `Statements` module; its definition
import supplies the comap construction. There are no additional mathematical
hypotheses or helper declarations.

This adapts Naganori Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`, lines 120–124](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean#L120-L124),
with ambient context at lines 53–64 and 110–118. Worker 256 read the entire
344-line source. The proof follows the source's `rfl`, adapting only imports,
the `Langlands.NYLL` prefix and the introduction of the closed target's
binders. Worker 122 supplied the closed-target proof guidance. The statement
and all published dependencies are unchanged.

The source file SHA-256 is
`bc2b582cac15fc4a9c6dc94e9687368e2a1bf91ca9d4111d41a9458fe8e49889`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original copyright and author header are preserved. Apache-2.0 applies;
the existing [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
The Lean header records the modifications by Worker 256 on 13 November 2026.
The approved check environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
This is a support proof for valuation subrings; it makes no host reciprocity
or class-formation assertion.
