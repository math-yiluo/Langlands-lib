# The same centralizer on a restricted standard-Levi apartment

This is an internal adapter for the standard-Levi clause of the Renard Cartan comparison. It uses only the published algebraic centralizer factor, literal valuation restriction, and compactness under closed rational-point embeddings. It proves no inherited special vertex, Levi building realization, or Cartan decomposition.

`standardLeviCentralizerDatum` packages the actual ambient centralizer as the centralizer of the same torus in the fixed standard Levi. Its group scheme, torus map, restriction-evaluation bijectivity witness, centralizer valuation and norm kernel are unchanged. Its inclusion is `standardLeviCentralizerFactor`; the represented-centralizer identity, closedness and factorization are the published results in `RenardCartanAlgebraicComparison`.

`isOmegaCompatible_standardLevi_of_restriction` transfers the full V6 identity from an ambient apartment to a supplied Levi apartment when each Levi valuation point is literally the restriction of an ambient point in the published `IsLeviRestriction` sense. Relative-root containment follows from the represented Levi inclusion. `RelativeRoot.comp_mem_subgroup` carries each Levi root-group point into its ambient root group. The two evaluations in V6 then become the ambient evaluations, and the factor identity makes conjugation use the same ambient centralizer point. The translation is unchanged because the centralizer's torus map and character valuation are unchanged. No building-level axiom is needed for this transfer.

`isCompact_specialCompactLeviSubgroup` proves compactness of the exact preimage of the fixed ambient compact subgroup, in the canonical rational-point topology of the actual standard Levi. It uses `isClosedEmbedding_rationalPointMap` for the closed Levi inclusion and compactness of its preimage.

`specialCompactLeviCentralizer_comap` composes the centralizer and Levi point maps, reducing the preimage of the same Levi compact intersection to the ambient centralizer preimage. The published `specialCompactCentralizer_comap` identifies the latter with the actual `rationalCommonNormKernel`. This identification does not assume any special-compact-preimage equality with a restricted Levi apartment.

The provenance is an internal derivation from the named Library results and predicates. The additional apartment and compactness hypotheses remain explicit; this unit is supporting work and does not prove `AvailableRenardCartanStatement`.
