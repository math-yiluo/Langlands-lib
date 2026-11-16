# The only remaining conditional local rank-one E₇ marking

For an actual Tits index over a nonarchimedean local field, of split rank
one, and with an equivalence of its actual simple vertices to Mathlib's
numbered E₇ Cartan matrix, assume
`LocalAnisotropicCartanComponentsStatement`. The theorem proves that the
exact distinguished set is vertex 1, in zero-based numbering, and that
every element of the full absolute Galois group fixes every vertex. It
holds in every field and residue characteristic, at an arbitrary universe.

The five-step walk-count argument of `CartanE7Root` gives Cartan rigidity,
which makes the full star action trivial. The actual rank-one orbit
comparison then makes the distinguished set a singleton.

The sixteen-reflection certificate gives an actual root with coefficients
`(2, 2, 3, 4, 3, 2, 1)`. Restriction to the actual maximal split torus
removes all terms except the distinguished coefficient. At vertices 2, 3
and 4 the coefficients are 3, 4 and 3; the relative-root multiple bound
excludes each. At vertices 0, 5 and 6, the branch vertex 3 and its three
distinct neighbors 1, 2 and 4 are all zero. The explicit component premise
and the actual anisotropic-kernel comparison exclude that configuration.
Vertex 1 is the only remaining possibility. The proof records its exact
marking together with full-star triviality.

This is an internal deduction from the proved finite rigidity, reflection,
rank-one orbit and root-multiple results, conditional on the stated
component premise. The remaining marking has coefficient 2 and zero
subdiagram A₆, so the argument does not exclude it. This theorem proves
neither that component premise, the absence of rank-one E₇ groups, nor the
unconditional local rank-one enumeration. It uses no downstream
classification or Kneser–Tits theorem.
