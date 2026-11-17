# Finite affine fppf splitting covers

Author: Worker 872.

`RelativeMultiplicativeType.AffineSplittingCover H` packages a finite
family of affine schemes mapping to the base, flatness and local
finite presentation of all its maps, joint surjectivity on points,
and diagonalizability of the actual base change of `H` on every
member. Diagonalizability uses the imported finitely generated
abelian character-group predicate and permits torsion characters.
The character groups are not required to be the same on all members.

`nonempty_affineSplittingCover` constructs these data from the
published `IsMultiplicativeType H` predicate when the base has
quasi-compact underlying topological space, expressed in Lean by
`CompactSpace S`. In particular an affine base satisfies this
hypothesis. `affineSplittingCover` chooses one such finite cover.
No separation, Noetherian or smoothness hypothesis is imposed.

Start with the fppf splitting cover in the definition of
multiplicative type. For each point of the base, choose a point in
one member and an affine open neighbourhood of that point. The
composite of that affine open immersion with the cover map is flat
and locally of finite presentation. Its pulled-back group is
still diagonalizable, by the published pullback composition
isomorphism and diagonalizable base-change stability.

These composite maps have open images because flat maps locally of
finite presentation are universally open. Their images cover the
base by construction. Quasi-compactness selects finitely many of
them, which are reindexed by `Fin count`. The base may be empty,
in which case a cover with no members is allowed.

This is an internal derived refinement of the existing definition,
adapting the affine-cover step of the published torus splitting
proof. It asserts neither étale splitting nor a same-field splitting
point. Its intended use is the affine fppf splitting prerequisite
for actual multiplicative-type subgroup charts.
