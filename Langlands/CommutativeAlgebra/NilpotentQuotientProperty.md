# Morphism properties on nilpotent quotients

`nilpotentQuotient_of_squareZero` applies to a morphism property `P` on the category of commutative rings in any fixed universe. Assume `P` contains identities, is closed under composition, and respects isomorphisms. If every quotient map `A → A/I` with `I² = 0` has `P`, then every quotient map by a nilpotent ideal has `P`. The hypothesis is uniform over all commutative rings in that universe; no hypothesis on a single fixed ring would suffice for this induction.

The proof uses Mathlib's `Ideal.IsNilpotent.induction_on`. In its composition step, for ideals `I ≤ J`, the quotient by `J` is the composite of the quotient by `I`, the quotient by the image of `J` in `A/I`, and the canonical double-quotient ring isomorphism. Multiplicativity handles the first two maps and invariance under isomorphisms handles the last.

This is an internal auxiliary result derived from the existing Mathlib nilpotent-ideal induction and double-quotient equivalence. It introduces no additional literature assertion. It supplies the ring-theoretic induction needed to pass from a square-zero lifting property to nilpotent lifting; it proves no square-zero lifting theorem itself.
