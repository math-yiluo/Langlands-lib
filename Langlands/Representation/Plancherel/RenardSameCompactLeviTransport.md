# Direct Cartan transport to the fixed ambient compact Levi intersection

This internal derived construction uses the supplied standard-Levi apartment
`DM` and `standardLeviParahoricData` from the published Library. It retains the
ambient centralizer scheme, torus map, character valuation, and centralizer zero
subgroup.

`sameCompactLeviCartanComparison_of_parahoric` assumes parahoric Cartan
conclusions on this Levi datum, inclusion of its parahoric at the supplied point
in the preimage of the original ambient special compact subgroup, and
compactness of that ambient subgroup. It proves the exact coverage and
norm-kernel classification for that preimage,
`SameCompactLeviCartanComparison`. No equality between the preimage and the
Levi's own special compact subgroup is needed.

The general helper `compactCartanComparison_of_parahoric_and_comap`
specializes `compactComparison_of_parahoric` to any parahoric building datum
and any larger subgroup with the stated centralizer preimage. The Levi
theorem then applies that helper to `standardLeviParahoricData`. The centralizer
intersection is the unchanged ambient norm kernel by
`specialCompactLeviCentralizer_comap`. Norm-kernel points fix the Levi
apartment point by full V6 and normalize its parahoric by
`normalizerStabilizer_mem_parahoric_normalizer`; the needed zero-normalizer
normality is supplied by `normal_normalizerZero`. Parahoric coverage and
classification give the two smaller-subgroup inputs, and
`dominantCentralizer_mul_normKernel` supplies stability of the actual dominant
set. The generic transport theorem then proves the larger-subgroup comparison.

`sameCompactLeviChamberEquiv_of_parahoric` constructs the resulting actual
valuation-chamber equivalence with double cosets of the fixed ambient compact
intersection. Its value theorem records that a dominant centralizer point's
valuation maps to the double coset of the same point under the canonical
centralizer factor into the actual standard Levi.

This is a source-free composition of published results. Levi parahoric Cartan,
the parahoric inclusion, and ambient compactness remain explicit hypotheses.
It proves neither inherited Levi building geometry nor the full
`AvailableRenardCartanStatement`.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
