# Orbital integrals of corrected support representatives

This internal specialization applies the actual source-cut integral square to
the actual corrected normalized-induction support representatives. Fix the
supplied field and topology, a smooth ambient complex representation `A`, source
and target shapes `B,C`, an inversion-length upper set `θ`, and `w` such that
`θ \ {w}` is also upper and `w` belongs to the corrected two-sided Weyl support.

`correctedOrbitRestriction` is the actual corrected induction-orbit isomorphism
applied after the canonical projection of the upper support to its quotient by
the lower support. Its value at a target-parabolic element `q` is the original
function at `w⁻¹*q`, using the actual permutation matrix. Compact support and
covariance come from that isomorphism.

For `B.cuts ⊆ D.cuts`, the actual normalized cut map preserves the corrected
support. `correctedOrbitRestriction_cutMap_eval` applies the previously proved
representative square to this specific restriction: the target restriction is
pointwise the actual Jacquet quotient projection of the source restriction.
Thus there is no additional assumed pointwise compatibility.

When `w` is increasing on each block of `B`,
`correctedOrbitRestriction_integral_cutMap` applies
`cutOrbitStagesIntegral_map` to these actual restrictions and the proved
pointwise equality. It identifies the target integral with the actual nested
coefficient projection of the source integral. Both integrands are the genuine
compact stages slices; the target measure is the pushforward of one supplied
source quotient measure along the actual quotient-coordinate homeomorphism.
The supplied measure is required to be finite on compact sets.

The construction is valid for arbitrary primes, supplied fields and topologies,
independent field and coefficient universes, and every natural rank including
zero. It uses no classification or irreducibility input. Compatible Haar data,
the comparison of these integrals with simultaneously selected orbit
equivalences, exterior signs, lower-degree exactness, terminal homology and
signed effectivity remain separate obligations.
