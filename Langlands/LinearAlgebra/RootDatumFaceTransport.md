# Based face heights under full root-data equivalences

This derived construction concerns arbitrary full integral root data, with arbitrary additive character and cocharacter lattices and no group-scheme premise. Supply a full root-pairing equivalence from `P` to `Q` and a base `b` of `P`.

`weight_mem_rootSpan` proves that the full weight equivalence maps the integral root span into the target integral root span. It uses the root-matching equation on the generators and induction on the integral span. `rootSpanMap` is the resulting linear map of integral root spans, retaining the exact full weight-lattice map. It sends every supplied root to its matched root.

`height_map` shows that ordinary based root heights agree after matching root indices and mapping the base. It maps an integral simple-root expansion through the full weight equivalence, reindexes the finite sum by the root-index equivalence, and applies the base-height expansion formula. `isPos_map_iff` consequently identifies the two positive root predicates.

`faceHeight_map` proves the precise naturality equation for the unscaled integral face-height form: the face height for the mapped base and transported coweight, composed with `rootSpanMap`, is the original face height. The transported coweight uses the inverse of the equivalence's contravariant coweight map. The proof compares the two linear maps on the integral simple-root basis, where each height is the indicator of nonvanishing of the simple-root pairing, and applies pairing compatibility.

No canonical choice of base, coweight, or equivalence is asserted. The result supplies transport of exact unscaled face heights and positivity, not compatibility of actual geometric filtration terms by itself.

Provenance: direct internal derivation from Mathlib's full root-pairing equivalences and mapped bases, integral simple-root expansions, and the existing definition of the face-height linear form.
