# Filtered symmetrization and actual compact invariant lifting

Author: Worker 94. This is an internal derivation from the actual symmetrization, conjugation, finite-span integration and symmetric Haar averages in the imported modules.

The construction uses the full complexification of the actual archimedean matrix Lie algebra, its whole symmetric algebra and its genuine universal enveloping algebra. The ambient field `K : Type u` and natural rank `n` are arbitrary; the averaging and finite-continuous-orbit results additionally assume `NumberField K`. Every compact component and rank zero are retained.

`lieSymmetricDegreeFiltration K n d` is the span of actual symmetric generator monomials of length at most `d`. Conjugation maps each such monomial to the monomial of its conjugated generators and extends by span induction. This proves preservation of each bound. The inverse group element gives the inverse of `lieSymmetricDegreeConjugation` on that span.

`lieSymmetricAlgebraSymmetrizeDegree` specializes the previously constructed filtered whole symmetrization to the actual Lie algebra over the complex numbers. It is onto the entire genuine enveloping degree piece, and its value agrees with whole symmetrization after coercion. Whole equivariance gives its equivariance against the actual degree-restricted conjugation on both sides. This establishes surjectivity, without an injectivity or PBW assertion.

For a genuine enveloping element, choose a whole symmetric preimage under the already proved surjective symmetrization. Its full-group conjugation orbit is the linear image of the symmetric conjugation orbit, by equivariance. Existing finite continuous symmetric orbits therefore give `envelopingConjugation_hasFiniteContinuousSpan`. Restriction to the full compact subgroup yields finite continuous orbits for `envelopingCompactRepresentation`. No topology on the enveloping algebra is imposed.

Use the Borel measurable structure and Haar measure normalized on the compact subgroup's whole space. Finite-span integration defines `envelopingCompactAverage` with values in the actual compact fixed enveloping subalgebra. Left invariance gives this fixedness, and normalization makes the average the identity on fixed vectors. Naturality of averaging for the actual equivariant linear symmetrization gives `envelopingCompactAverage_symmetrize`, using the same normalized Haar measure as the existing symmetric average.

The private integration lemma proves that a finite-span integral belongs to every complex submodule containing all its integrand values. Apply the quotient map by that submodule, compose with arbitrary algebraic dual functionals, and use that every scalar integrand is zero. Dual separation in the quotient proves membership. Applied to the symmetric and enveloping degree submodules, it shows that both actual averages retain their respective degree bounds.

To prove `exists_compactInvariant_symmetrize_degree`, lift a compact fixed genuine enveloping element of degree at most `d` to a symmetric element with that bound. Average the preimage in the symmetric algebra. Averaging retains the bound and makes the preimage compact fixed; naturality and the fixed-vector identity show that its symmetrization is the original element. Exhaustiveness of the genuine enveloping filtration then gives `lieSymmetricCompactInvariantSymmetrize_surjective`.

This unit establishes compact invariant lifting, including the degree bound. It does not identify full-group invariants with the enveloping center, prove full-group invariant lifting, central or covariant generation, admissibility, or automorphic differential growth.
