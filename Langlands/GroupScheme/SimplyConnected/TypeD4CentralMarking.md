# Central marking when the full D4 action has no fixed leaf

This internal derived module concerns actual Tits indices over arbitrary
fields, at every universe and in every characteristic. An equivalence
`e : d.Vertex ≃ Fin 4` must identify every actual Cartan entry with
`CartanMatrix.D 4`. Vertex `1` is the center; vertices `0`, `2` and `3`
are the leaves.

`not_D4_leaves_distinguished` assumes split rank one and rules out the
complete distinguished subset being exactly the three leaves. It does
not require a hypothesis about the star action.

The implemented proof names the four simple root indices `a i`. If all
leaves are distinguished, their restrictions are the same nonzero
character `beta` by `rootRestriction_eq_of_rank_one`, while the center
restricts to zero. Starting with the central root, reflect successively
in leaves `0`, `2` and `3`. Each intermediate index is an actual root
because `reflectionPerm` is a permutation of the actual root indices.
The center-leaf Cartan entries are `-1` and the leaf-leaf entries are
zero. Invariance of the pairing under reflection therefore gives pairing
`-1` at each step. Applying `rootRestriction_reflection` shows that the
three successive restrictions are `beta`, `2 • beta` and `3 • beta`.
The last equality contradicts
`rootRestriction_ne_nsmul_of_three_le` for the distinguished leaf `0`.
This argument uses the root pairing even when the relative root system
is nonreduced, and retains characteristic two.

`D4_central_marking_of_no_fixed_leaf` additionally assumes that no leaf is
fixed by every automorphism of the separable closure over the ground
field. The existing `D4_marking_cases_of_no_fixed_leaf` then makes the
entire distinguished subset either the center or all three leaves.
The preceding contradiction removes the second case. The conclusion is
the exact `IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) e`
predicate, including every Cartan entry and both directions of the
distinguished-subset comparison.

These are consequences of the actual full star action, the rank-one
distinguished-orbit theorem, and the published bound on positive relative
root multiples. They do not rule out a transitive leaf action or prove
the local arithmetic exclusion of trialitarian groups.
