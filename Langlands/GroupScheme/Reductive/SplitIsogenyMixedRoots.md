# Mixed simple roots for a restricted target-torus action

This is a derived extension of `SplitLeviGluingMixedRoots` to the target
conjugation action restricted along the prescribed torus map of a root-datum
isogeny. A strict mixed combination of distinct source simple roots lies in
neither sign of the nonnegative simple-root monoid. Every source root has
one sign in that monoid, as does every nonnegative integral multiple of it.
Thus no strict mixed character is a multiple of a source root.

`mem_roots_comp_iff` expresses any root of the restricted target action as
the restriction of a target root. The actual character-map equation and
`root_weightMap` identify that restriction with a characteristic-power
multiple of a source root. The previous exclusion applies without requiring
transport of simple systems. Semigroup weight vanishing then proves that
the mixed semigroup subgroup is trivial on all scheme tests. The published
semigroup commutator theorem proves commutation of the restricted target
root functors at distinct source simple/opposite characters.

For the actual graph, root-lift inclusion in its intrinsic source-torus
root functor is preserved under each projection. The first projected pair
commutes by the source mixed-root theorem. The second projected pair
commutes by the restricted target theorem proved here. Joint injectivity
of the graph projections proves `commute_positive_negative` on every test.
`CommutingSimpleIsogenyGraph` retains the same graph and this certificate;
`commutingSimpleIsogenyGraph` constructs it from the stated root data and
actual character-map equation.

The construction retains arbitrary fields and the actual root factors.
This supporting unit does not prove the host realization theorem.
