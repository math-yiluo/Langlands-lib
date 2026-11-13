# Specialness from zero root-jump witnesses

This is an internal geometric consequence of the published root-lifting and
apartment interfaces. It applies over an arbitrary field extension `K/k`, to
split tori `S` and `T_K` mapping monomorphically into `G` and `G_K`, with the
commuting torus inclusion `f`, affine locally finite type `G`, and supplied
apartment data `DS` and `D`. All universes are arbitrary. The upper affine
structure is an explicit parameter.

`SpecialPointRootJumpDescentStatement` asserts specialness of a chosen lower
point `w` from specialness of a chosen upper point `x` and the following
pointwise root-jump assumption: every upper ordinary affine root vanishing at
`x`, whose derivative after `torusFieldTranslationMap` is nonzero, admits a
lower relative root and an actual rational root-group point of value zero at
`w`, with equal derivative kernels on the unreduced real cocharacters of `S`.
The lower root is allowed to be proportional to a given root. The statement
assumes the root-jump witnesses; this module does not construct them or prove
`UnramifiedRootJumpDescentStatement` or `UnramifiedSpecialPointDescentStatement`.

`rootForm_comp_torusFieldTranslationMap` proves that character restriction
identifies the pulled-back root forms, using `eval_descentCocharacterMap` and
`eval_splitCocharacterBaseChange`. `ker_eq_of_comp_mkQ` reflects equality of
kernels through the surjective lower root-annihilator quotient map.

The proof `isSpecialPoint_of_rootJumpDescent` proceeds direction by direction.
It lifts the lower relative root with `splittingFieldRootLift` and its character
restriction identity from `AbsoluteRootRestriction`. The upper apartment has
an ordinary affine root in that direction. Upper specialness supplies a
parallel ordinary root vanishing at `x`. Pulling back kernels yields a nonzero
restricted derivative and identifies its kernel with that of the original
lower direction. The assumed root jump supplies a lower root-group point of
value zero. `affineFunctional_mem_extendedAffineRoots` constructs its extended
affine root. Injectivity of split root forms identifies the resulting relative
root, and the published doubling lemmas supply an ordinary affine root with
the same kernel and value zero at `w`. Surjectivity of the lower quotient then
reflects the kernel equality to the reduced translation space. The kernel
criterion for specialness finishes the proof.

No cross-field descent theorem is used. The root-jump hypothesis is the
remaining arithmetic input; the proof here is the geometric assembly only.
