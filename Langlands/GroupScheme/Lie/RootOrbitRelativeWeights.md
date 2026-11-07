# Actual relative weights from a whole Galois root fiber

This internal construction connects the literal ambient orbit span with an
entire original relative weight space, conditional on the orbit being the
whole root-restriction fiber. It uses the published split-torus weight
decomposition, actual fixed-orbit reconstruction and effective Galois descent.

For two split tori over a field, `weightSpace_comp_eq_iSup_roots` refines the
published character-fiber decomposition at a nonzero restricted character.
A character in that fiber cannot be zero. If its weight space is zero, it
contributes nothing to the supremum; otherwise it is an actual root. The
reverse inclusion uses the original decomposition's fiber indices.

Now let `S` and `T` be original commutative group schemes over a field `k`,
let `f : S -> T` and `j : T -> G` be the actual maps, and extend to a field
`L`. The ambient group is affine and locally of finite type. Assume that
`S` and `T_L` are split and that the original character `a` is nonzero.
For an actual root `beta` over `L`, assume explicitly that its ordinary
Galois orbit equals `rootRestrictionFiber k L j f a`.

`rootOrbitWeightSpan_eq_weightSpace` then identifies its literal ambient
orbit span with the entire actual weight space for the base change of the
restricted action and character. The proof reindexes the root-fiber
decomposition through the assumed equality of sets. Splitness of `S`
ensures that the base-changed character remains nonzero. Neither finite
degree nor Galoisness is needed for this equality.

`rootOrbitFixedWeightSpaceEquiv` carries the underlying Lie vector
unchanged through this equality. Both fixed carriers impose fixedness
under the same canonical ambient Galois maps, so their additive structures
and inverse identities follow directly.

When `L/k` is finite Galois, `G` is connected reductive and `j` is a maximal
torus, `rootOrbitFieldWeightSpaceEquiv` composes three constructed additive
equivalences: from the actual root-stabilizer fixed field to the actual
fixed orbit span, to the fixed base-changed weight space, and back to the
entire original weight space. Its base-change theorem identifies the
extended original vector with the literal ambient orbit vector used to
construct it. The construction is uniform in the common universe and
characteristic.

The whole-fiber equality is a visible premise, not a quasi-split
transitivity theorem. No field character or its centralizer action,
root-group point coordinates, or apartment is constructed here. Those
remain obligations of the unchanged apartment-existence task.
