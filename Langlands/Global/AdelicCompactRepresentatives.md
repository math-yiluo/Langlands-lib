# Compact representatives for the actual additive adele quotient

`exists_compact_sub_diagonal_mem` exposes the compact fundamental set used in the
published proof `adeleQuotientCompact`. This is an internal derived lemma; it
uses the actual completions and restricted-product topology without changing the
quotient or its diagonal embedding.

The set is the product of `archimedeanFundamentalSet K` and
`integralFiniteAdeles K`. First subtract a field element to make the finite
coordinates integral. Then subtract a global integer to move the infinite
coordinates into the archimedean fundamental set. The second subtraction
preserves finite integrality. Compactness is the product of the already proved
compactness results for the two factors. This is precisely the representative
construction in `AdeleQuotientCompactProof`, whose paired Markdown provides its
original-source provenance.
