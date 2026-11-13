# Sylow subgroups from a split Tits-system Borel

This internal finite-group construction uses the existing Tits-system
rigidity theorem and the normalizer condition for finite p-groups.

Let `(B,N,π,S)` be a Tits system on a group `G`. Suppose `U ≤ B`, `B`
normalizes `U`, and every element of `B` is a product `u t` with `u ∈ U`
and `t ∈ ker π`. Then `normalizer_eq_of_split` proves `N_G(U) = B`.
Bruhat decomposition writes an element normalizing `U` as `a n b` with
`a,b ∈ B` and `n ∈ N`. The representative `n` also normalizes `U`.
Conjugation by `n` preserves `ker π`, and hence preserves `B = U ker π`.
Tits-system conjugacy rigidity puts `n` in `B`, so the original element
belongs to `B`.

Now assume `G` is finite, `p` is prime, `U` is a p-group, and every p-subgroup
of `B` is contained in `U`. For any p-subgroup `P` containing `U`, the subgroup
`P ∩ N_G(U)` is a p-subgroup of `B`, so it is contained in `U`. Thus `U`,
viewed in `P`, is self-normalizing. A finite p-group is nilpotent and satisfies
the normalizer condition, forcing `U = P`. This proves
`maximalPSubgroup_of_split`.

`sylowOfSplit` bundles precisely the original `U` as a `Sylow p G`.
Its subgroup is definitionally `U`. The Borel p-subgroup criterion remains
an explicit premise, to be supplied in reductive-group applications by the
torus quotient of a Borel.
