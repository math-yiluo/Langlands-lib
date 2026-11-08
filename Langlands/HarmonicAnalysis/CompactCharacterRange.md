# Surjectivity detected by compact-group characters

This internal auxiliary construction implements the compact-dual averaging step
in Worker 1843's plan for restriction matching. It uses the previously developed
Stone–Weierstrass density of the span of a separating character subgroup.

The construction `average` integrates a continuous complex function along a
translate of a continuous homomorphism from a compact group. A probability
measure makes this a continuous complex linear functional of norm at most one.

The theorem considers a continuous homomorphism between compact Hausdorff groups
and a subgroup of the target's continuous circle characters separating its
points. It assumes that only the trivial character in this subgroup pulls back
to the trivial character. For the normalized Haar measure on the source,
nontrivial pullbacks have integral zero by translation invariance. Consequently
averaging along any translate of the homomorphism agrees with averaging along
the homomorphism on every character in the subgroup. The agreement extends by
linear closure and Stone–Weierstrass density to all continuous complex functions.

If a point lay outside the image, that image and its translate by the point
would be disjoint compact closed sets. Urysohn's lemma supplies a real function
zero on the image and one on its translate. Its complexification contradicts
the equality of the two averaging functionals. The homomorphism is therefore
surjective. All compactness, topology and character-detection assumptions are
explicit; this helper does not assert an arithmetic input by itself.
