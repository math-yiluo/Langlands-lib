# Vanishing ideals of actual global functions

This is a derived supporting construction for the homogeneous-quotient affineness argument. It uses Mathlib's actual global-section ring and canonical map to its spectrum; no external theorem is transcribed.

For any scheme `X` and any set `Z` of its points, `globalVanishingIdeal X Z` is the prime-spectrum vanishing ideal of the image of `Z` under `X.toSpecΓ`. Its elements are exactly the global functions `s` such that every point of `Z` lies outside `X.basicOpen s`. This definition and membership characterization require neither affineness nor reducedness.

If a scheme morphism `f : X ⟶ Y` maps `Z` into `W`, then pullback sends the global vanishing ideal of `W` into that of `Z`. The proof uses the exact pullback formula for principal opens. A nonempty set has a proper global vanishing ideal, since the constant function one vanishes nowhere.

When `X` is affine and `Z` is closed, the zero locus of its global vanishing ideal is exactly `Z`. The proof transports the prime-spectrum zero-locus/vanishing-ideal correspondence through the canonical affine isomorphism. Consequently two disjoint closed sets in an affine scheme have comaximal global vanishing ideals: a prime containing their sum would give a point in both sets. No finiteness, field, or characteristic hypotheses are imposed.

These lemmas provide only the geometric ideal interface. They assert neither reductivity nor affineness of any homogeneous quotient.
