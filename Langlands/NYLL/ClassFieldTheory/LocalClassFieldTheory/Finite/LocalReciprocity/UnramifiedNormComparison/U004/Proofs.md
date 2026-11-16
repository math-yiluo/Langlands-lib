# NYLL M267.004: canonical comparison proof

`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_surjective` proves exactly
`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_surjectiveStatement`.
Every unramified valuation class is represented by an actual norm quotient class.

## Implemented proof

The proof introduces the original Type-zero fields and all fifteen instance arguments. The published normQuotientLift_surjective sends surjectivity of the actual projection to surjectivity of its descended map. The kernel condition is proved by the published localNormSubgroup_le_unramifiedNormSubgroup and unramifiedNormClass_eq_one_iff_mem, exactly as in the canonical map definition. Mathlib QuotientGroup.mk'_surjective supplies surjectivity of unramifiedNormClass, which is definitionally that quotient projection. This replaces the source M266.014 wrapper unramifiedNormClass_surjective with its underlying Mathlib result, retaining the same quotient and all hypotheses.

The target quantifies over K L : Type and the original fifteen instance
arguments: the two fields, their valuation relations, topologies and local-field
certificates, the algebra structure, finite dimensionality, Galoisness, valuation
extension, integral closure and finite integer-ring module, and the published
unramifiedness class. These are the hypotheses of the imported closed target;
none is added or removed. No global or local instance is introduced here.
The map and quotient objects are reused by their adapted Lean names.

## Source and modifications

Original source: `LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_surjective`, lines 81–92,
with shared telescope lines 34–44 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The pinned whole-file SHA-256 is
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
The readable copy belongs to `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`.

Worker 205 adapted this proof on 16 November 2026 by prefixing the namespace,
importing the focused target and required published dependencies, introducing
its closed telescope and omitting unrelated declarations and the redundant
noncomputable section. The source M266.014 projection-surjectivity wrapper is replaced by Mathlib's `QuotientGroup.mk'_surjective`, preserving the same lifted-map proof.
The original docstring, copyright and author header remain, with this dated
modification record and focused documentation added. Original license and
notices remain at `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Worker 563 prepared the proof pair for submission from Worker 205's shared draft revision 1, checking it against the pinned source and the published target. The Lean proof is unchanged from that draft. This contribution contains only the proof pair; its dependencies and target are imported from the Library.
