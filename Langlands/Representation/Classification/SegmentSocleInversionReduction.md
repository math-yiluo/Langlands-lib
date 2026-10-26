# Actual segment-product embeddings and inversion reduction

This internal auxiliary module connects actual segment-product data with their occurrence-sensitive lists. It does not prove a local representation-theoretic reduction or multisegment socle exhaustion.

`HasSocleEmbedding` requires actual socle blocks and a genuine irreducible embedding into their full normalized upper product. It imposes no ordering. `SocleEmbeddingList` records a datum at the fixed rank realizing the specified list, including every segment occurrence with its attached actual block.

`SegmentProductDatum.multisegment_degree` proves that the associated multisegment has the datum's fixed rank. It rewrites the sum of the mapped occurrence list as the original finite sum and uses the datum's degree-sum field.

The adjacent-list lemmas identify the original finite indices from a displayed prefix, two adjacent segments, and suffix. The permutation theorem proves equality of the swapped list by checking every index. Only the two adjacent positions change; repeated segment values are allowed and no occurrence is removed. The imported `permute` construction carries each block with its original segment, so this identity concerns the actual permuted datum.

`HasIndexedSocleEmbeddingReductions π` explicitly specifies two unproved representation-theoretic rules, for every actual datum carrying a socle embedding of this fixed `π` and every adjacent index:

- An unlinked pair may be interchanged by the datum's actual adjacent permutation while retaining a socle embedding of `π`.
- For a preceding pair, either that interchange retains the socle embedding, or there are a union segment `U`, an optional intersection segment `I`, and replacement data at the same rank with a socle embedding of `π`. Their list is exactly the old prefix, `[U]`, `I.toList`, and the old suffix. The imported `IsUnionIntersectionReplacement` requires the exact union support, and either an empty intersection for `none` or the exact intersection support for `some`.

`HasIndexedSocleEmbeddingReductions.hasLocalSegmentReductions` transfers those indexed hypotheses to `SocleEmbeddingList`. It recovers the adjacent indices from the displayed list decomposition and uses the occurrence permutation identity in the swap cases. In the replacement case the original `take` and `drop` are exactly the displayed prefix and suffix. The replacement datum itself supplies its actual blocks and degree-sum witness.

`HasIndexedSocleEmbeddingReductions.exists_ordered` assumes that indexed interface, an inhabited collection of actual embedding data, and integral twist freeness at the matching universes. It applies the imported conditional inversion-minimization theorem to the realized lists, then recovers the actual datum and converts list ordering to its original finite-index ordering. There is no finiteness assumption on the embedding collection. This theorem does not establish its indexed interface or nonemptiness.

The elementary strong-socle lemma uses equality of images: if one irreducible embedding has the defining strong uniqueness property, another irreducible embedding into the same ambient representation has it too. `HasSocleEmbedding.isZelevinskySocle_of_exists` applies that lemma after an actual strong socle of the datum is supplied. Its existence premise includes the datum's ordering. No isomorphism-class classification or existence assertion is proved by this transport.

The field universe `uF` and segment-carrier universe `uV` remain independent. Segments have carrier universe `uV`; block and output representations have the actual induced carrier universe `max uF uV`. Choosing `uV := max uF uV` specializes to the saturation required by the parent exhaustion task. Every construction retains the supplied topology and actual normalized upper induction.

Provenance is internal. These are consequences of the published segment-product structure, the actual simultaneous permutation of segments and blocks, list indexing, the imported conditional minimization API, and the defining image equalities of the constituent relations. The direct imports are `SegmentInversionMinimization` and `SegmentProductPermutation`. Their lower dependencies supply segment definitions, explicit conditional freeness and combinatorics, and normalized induction constructions. No excluded special-head, analytic segment-classification, quotient-exhaustion, tempered-uniqueness or square-integrable-exhaustion proof is invoked. In particular this module does not import the integral-freeness proof; it retains the proposition as an explicit premise.

Local commutation, linked reduction, nonempty embedding collections, and ordered-product strong-socle existence remain separate mathematical obligations. This conditional auxiliary is not a proof of any of them or of the parent exhaustion statement.
