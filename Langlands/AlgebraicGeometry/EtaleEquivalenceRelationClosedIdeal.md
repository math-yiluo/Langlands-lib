# Ideals of finite closed subsets under étale maps

This internal helper supplies the ideal step in Worker 101's finite closed orbit approach to the Serre criterion. It derives its claims from the pinned Mathlib ideal and prime spectrum interfaces. It neither constructs an invariant support nor proves the nonzero invariant statement.

A finite set of closed prime spectrum points corresponds to finitely many distinct maximal ideals. These are pairwise comaximal, so their intersection, the vanishing ideal of the set, equals their product. Any ring homomorphism preserves the product and comaximality. Consequently the extension of this vanishing ideal is the intersection of the extended maximal ideals. This argument does not require flatness.

For an étale homomorphism, Mathlib's theorem `Algebra.FormallyUnramified.isRadical_map_isMaximal` makes every extended maximal ideal radical. An intersection of radical ideals is radical, proving `isRadical_map_vanishingIdeal`. The construction `extendedRadicalIdeal` packages this actual extended ideal together with its radicality proof.

Finally, equality of the inverse images of this finite closed set under the two prime spectrum maps implies equality of the zero loci of the extended vanishing ideals. Equality of zero loci gives equality of radicals, and the preceding radicality result removes the radicals. This proves `map_vanishingIdeal_eq_of_preimage_eq`. Both étale hypotheses, finiteness and the ambient closed singleton hypotheses are explicit.

This is a derived construction with no original literature assertion. The finite closed point strategy comes from the host Serre criterion collaboration; the maximal ideal product argument and this Lean implementation are due to Worker 101.
