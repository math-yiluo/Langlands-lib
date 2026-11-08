# Torus characters fixed by unit-valued normalizing points

This internal construction uses actual affine group schemes over an arbitrary
field and an actual commutative subgroup. The same embedding of that subgroup
in the ambient group factors through two supplied group homomorphisms. The
subgroup embedding is a monomorphism. No torus or Borel existence is asserted.

Supply actual rational characters on the two groups. A coordinate of the
ambient group is left covariant for the first character coordinate and right
inverse covariant for the second on every relative test scheme. Assume the
restrictions of these two characters to the common commutative subgroup are
additive negatives of one another. A supplied rational point normalizes that
subgroup and has a unit value under the ambient coordinate.

`isIntertwiningPoint_of_normalizer` derives the exact all-test intertwining
identity from the published normalizing-point equation and the two
factorizations. The automorphism in this identity is the inverse of the
normalizing automorphism: `j(t)n = n j(σ⁻¹(t))`. This fixes the action
convention needed by the published bi-covariant cancellation result.

That cancellation compares the two evaluated characters at every test point.
The inverse in right covariance cancels the negative sign of the second
restricted character. Thus the first restricted character has the same
value at `t` and at `σ⁻¹(t)`. Character separation on all tests makes this an
equality of actual characters. In the published Weyl-action convention,
this says the rational normalizing point fixes the corresponding element
of the full integral character lattice.

The definition `unitNormalizerFixedCharacter` constructs this character
together with its fixedness certificate. Its value is exactly the
restriction of the first rational character, as the accompanying theorem
states. The construction uses neither a density argument nor a claim about
differentials in positive characteristic.

The supplied covariance laws, actual characters and opposite-restriction
identity remain hypotheses. The file proves neither regularity nor
centralizer membership, and constructs no representation or Bruhat
decomposition. Those are the next consumer obligations. Its provenance
is the implemented internal deduction from published actual character
evaluation, normalizing automorphisms, inner conjugation, and bi-covariant
unit cancellation.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
