# Positive characters on an actual refined parabolic

For every prime, finite p-adic field realization, supplied compatible topology,
block shape and block refinement, a continuous character from the actual refined
parabolic to the positive real units is trivial on its actual unipotent radical.
Consequently it equals its restriction to the actual refined Levi section,
inflated through the published refined Levi projection. Rank zero and arbitrary
block refinements are included.

`refinedPositiveLeviCharacter` is precisely restriction along
`refinedLeviSection`. The field topology appears in the continuity hypothesis;
no compactness or factorization premise is imposed on the parabolic character.

This is an internal derivation for the normalization step in the local orbit
comparison. The proof uses the published
`refinedUnipotent_finite_containment` on the singleton containing the given
radical element. The restriction of the character is continuous on this actual
subgroup. The published `eq_one_of_isCompact` makes it trivial on the resulting
compact open subgroup and therefore at that element. Finally,
`refinedDecomposition` expresses each full parabolic element as its radical
part times its actual projected Levi section; multiplicativity proves the
factorization. The proof imports both published prerequisites by Lean name.
No orbit integral, Haar ratio or normalized comparison is asserted here.
