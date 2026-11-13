# Restriction preserves extension: proof of M233.007

The theorem
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension`
has exactly the closed published type
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtensionStatement.{u, v, w}`.
If the canonical valuation of a valuation subring `A` of `Ω` extends a
valuation `v` of `K`, the canonical valuation of its restriction to each
intermediate field `E` also extends `v`. The field and value-group universes
remain independent; the extension hypothesis remains an instance binder.

The implemented proof follows the source's ring-of-integers argument.
`Valuation.HasExtension.ofComapInteger` reduces the assertion to equality
of subrings of `K`. Extensionality and the comap/valuation membership rules
reduce it to membership of
`algebraMap E Ω (algebraMap K E x)` in `A` iff `v x ≤ 1`.
`IsScalarTower.algebraMap_apply` identifies this composite with
`algebraMap K Ω x`. The canonical valuation's `valuation_le_one_iff` and
`Valuation.HasExtension.val_map_le_one_iff` for the given extension close
the goal.

The sole direct import is the published `Statements` module, which imports
the restriction definition and `Mathlib.RingTheory.Valuation.Extension`.
The proof adds no hypotheses and needs neither M233.005 nor M233.006.
Compared with the source, its unused `mem_restrictIntermediateField_iff`
simp argument is omitted: the pinned Mathlib already simplifies the goal
without it, and including it triggers the unused-simp-argument linter.
Other changes introduce the closed telescope, prefix the namespace with
`Langlands.NYLL`, qualify Mathlib's valuation-subring names and use focused
imports.

Source: Naganori Yamaguchi, *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`, lines 132–148](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean#L132-L148),
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
