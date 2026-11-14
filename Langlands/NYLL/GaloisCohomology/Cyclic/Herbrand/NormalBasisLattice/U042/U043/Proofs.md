# NYLL M144.043: `exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension`

This proves exactly
`Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtensionStatement`
from `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements`.
The theorem uses the required source-adapted name and preserves the target’s
parameters and hypotheses. The published statement and its imports are unchanged.

## Source and attribution

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 705–783](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L705-L783).
The retained file is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`,
SHA-256 `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
it is also covered by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

The original copyright and author header is retained. The Apache-2.0 license
and notice are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 640 extracted this focused proof on 14 November 2026, added the
`Langlands.NYLL` namespace prefix, reduced the imports to the three published
modules below, and wrapped the conclusion in the published proposition
definition. The one unpublished source prerequisite, M144.042, is derived
locally as described below, without redeclaring its required theorem name.

## Implemented proof and dependencies

Write x as a/b with nonzero b in the actual valuation ring of L, using
`IsFractionRing.div_surjective`. The discrete valuation ring factorization
writes b as a unit times the m-th power of L's chosen uniformizer. Choose n=m.
The image of K's chosen uniformizer lies in L's maximal ideal: locally, its
irreducibility identifies K's maximal ideal with its span, and Mathlib's
`Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff` transfers membership.
This is the M144.042 input, derived inside the proof because that sibling
candidate is not yet published.

Raise that membership to the m-th ideal power and use the published
`maximalIdeal_pow_eq_span_uniformizer_pow L m` to express the m-th power of
the base uniformizer's image as c times the m-th power of L's chosen
uniformizer. Map these identities to L. Nonzero uniformizers and units permit
cancellation of the denominator; `field_simp` proves that the resulting
product is the image of `c * ↑ub⁻¹ * a` in L. This element belongs to the
valuation ring by its subtype membership. The map comparison unfolds
`integerRingMapOfValuationExtension` and uses preservation of powers, just
as in the source.

The direct imports are the published target module and
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs`
and `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U022.Proofs`.
They supply irreducibility of the chosen uniformizers and the maximal-ideal
power equality; Mathlib supplies fraction-ring representation, DVR
factorization and ideal membership. Both fields have their actual local-field
and valuation structures, with a valuation extension along the algebra map.
No finite-dimensional or Galois hypothesis is used. No new axiom or global
instance is introduced. This exact denominator-clearing support result
discharges no host class-formation, cup, transfer, Tate or reciprocity target.
