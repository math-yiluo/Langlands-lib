# The parabolic order correspondence for a unipotent quotient

Over an arbitrary field `k` in universe `u`, let `G` be a smooth connected
affine group scheme and `Q` an affine group scheme. Let `q : G ⟶ Q`
be flat, surjective, and locally of finite presentation, with smooth
connected unipotent actual kernel. Full inverse image along `q` is an
order isomorphism
`ParabolicFunctor Q ≃o ParabolicFunctor G`.

These are the existing actual parabolic subgroup functors: each is the
full range of a geometric parabolic embedding, and its order is inclusion
on every relative scheme test. No new parabolic predicate is introduced.
The forward order map has underlying functor `F.comap q`; the inverse
map has exact inverse image equal to its source argument. No perfectness,
reductivity, or restriction on characteristic is assumed.

This is an internal consequence of the actual geometric parabolic
correspondence in `Absolute/UnipotentQuotientParabolics`, together with
fpqc descent of represented subgroup containment. The Lean proof first
uses `isParabolicSubgroup_preimage` and the range identity for
`SubgroupPreimage.inclusion` to preserve parabolicity under full inverse
image. The paired helper `SubgroupFunctor/FpqcComap` reflects inclusion
because the target parabolic is represented by a closed immersion.
It therefore gives an order embedding.

For surjectivity, `exists_parabolic_image` constructs the actual image of
each source parabolic over the original field and supplies the exact
full inverse-image identity. `OrderIso.ofSurjective` then constructs the
order isomorphism. Its inverse-image identity follows by applying the
forward map to the chosen inverse.

`UnipotentQuotientParabolicOrderStatement` records this order isomorphism
and both explicit underlying-functor identities; the accompanying
`unipotentQuotientParabolicOrder` proves it. The other direct project
input, `Rational/ParabolicFunctor`, supplies the existing type and its
representative-independent meaning.

This focused algebraic result assumes the quotient and its actual kernel
properties. It constructs no integral model, facet association,
residue-torus lift, or prescribed-point apartment.
`UnramifiedFixedPointSplitTorusStatement` remains open.
