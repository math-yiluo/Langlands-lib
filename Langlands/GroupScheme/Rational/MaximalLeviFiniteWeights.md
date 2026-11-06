# Finite-weight coarsening of a proper cocharacter centralizer

The internal predicate `IsProperCentralizerCoarsening i zeta mu` requires
three all-test subgroup-functor comparisons. The dynamic parabolic of `mu`
contains that of `zeta`; its dynamic centralizer strictly contains that of
`zeta`; and its centralizer is not the whole group.

The theorem `exists_properCentralizerCoarsening` works with a smooth connected
affine group over an arbitrary field and any homomorphism from a split torus.
If the centralizer of `zeta` is strictly contained in the proper centralizer
of `eta`, it constructs such a direction `mu`. The torus need not be maximal,
and the target group need not be reductive.

The proof uses the published zero-root criterion
`dynamicCentralizer_le_of_root_zero_imp`, with its connectedness premise
discharged by `dynamicConnected`, and the converse implication
`relativeRoot_pairing_eq_zero_of_centralizer_le`. Thus every actual root
annihilating `zeta` annihilates `eta`, and strictness supplies a root that
annihilates `eta` but not `zeta`. Properness supplies a root nonzero on
`eta`, using the published `rootAnnihilatorCentrality`.

The finite-root theorem `IsSplitTorus.finite_relativeRoots` and
`exists_integral_boundary_combination` give integers `n > 0` and `m`.
Set `mu = n*zeta + m*eta`. The combination preserves nonnegative root
pairings and makes a new root zero. The published parabolic root-sign
criterion, again with `dynamicConnected`, proves the parabolic inclusion.
The zero-root criterion proves the strict centralizer inclusion.
The retained root that annihilates `eta` pairs with `mu` as `n` times
its nonzero pairing with `zeta`, proving properness.

This is an internal consequence of the named published structure theorems
and the finite arithmetic lemma; it invokes no external literature claim,
root-system classification, or root-negation assertion. It does not identify
dynamic parabolics with actual rational parabolics and does not prove
`MaximalLeviContainmentStatement`.
