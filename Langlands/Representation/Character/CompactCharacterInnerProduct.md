# Character pairings for smooth representations of compact groups

For two finite-dimensional smooth complex representations `ρ` and `σ` of a compact topological group with its Borel σ-algebra, `CompactCharacterInnerProductStatement` gives the integral of `χσ(k) χρ(k⁻¹)` against a left Haar measure `μ`. It equals the dimension of the space of intertwining maps from `ρ` to `σ` times the Haar volume of the whole group.

Both representations factor through a common finite quotient by an open normal subgroup. Pushed to that quotient, Haar measure has equal mass on every point by translation invariance. The integral is therefore the finite character pairing scaled by total mass. The finite character orthogonality formula computes this pairing, and the quotient map is surjective, so the spaces of intertwining maps before and after factoring have the same dimension. Positivity of the Haar volume gives `compactCharacterInnerProduct_ne_zero_iff`.

This supplies the character pairing for restrictions to a common compact subgroup in the interaction test for two compact types in Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, University Lecture Series 16, 1999, §14, Lemma 14.1, p. 71.
