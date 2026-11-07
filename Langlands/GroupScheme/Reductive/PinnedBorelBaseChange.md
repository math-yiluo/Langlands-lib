# The actual chosen Borel under scalar extension

For arbitrary fields `k` and `K` in universe `u`, an algebraic extension
`K/k`, an actual affine group scheme `G` over `Spec k`, and a supplied
complete split pinning `p`, `negativeBorelBaseChangeIso` compares the actual
pullback of `p.negativeBorel` with the negative Borel chosen from `p.baseChange`.
Its inclusion equation is
`negativeBorelBaseChangeIso_hom_comp`: composing the comparison with the new
inclusion gives the pullback of the old inclusion.

The construction is an internal consequence of the published full-lattice
pinning base change, root-height formula, root-sign inclusion theorem and
dynamic subgroup base change. `baseChange_height` transports an integral
simple-root expansion through the character-lattice homomorphism. The simple
support is unchanged, so the sum of its coefficients, and hence root height,
is unchanged.

The chosen positive cocharacters need not themselves be equal under scalar
extension. Their pairings with each root are positive integral multiples of
that root's height. `baseChange_positiveCocharacter_pos_iff` therefore proves
that their positive root pairings have identical signs. Negation turns this
into equivalence of nonnegative pairings for the two reversed cocharacters.
Every actual relative root is a root of the pinning's full root datum, so the
published `relativeRootSignInclusions` proof applies to all relative roots.
Both subgroup inclusions then give
`parabolic_baseChange_opposite_positiveGm`, equality of the actual dynamic
parabolic subgroup functors.

Dynamic parabolic base change shows that the old Borel's pulled-back inclusion
represents this same functor. Uniqueness of representing subgroup inclusions
constructs `negativeBorelBaseChangeIso` and its inclusion equation.
`range_baseChange_negativeBorelHom` consequently identifies their subgroup
ranges on every relative scheme test.

The supplied complete pinning includes connected reductivity and an actual
split maximal torus. The construction uses no perfectness or characteristic
premise. It supplies a comparison for existing pinnings; it does not construct
pinnings, a semilinear cocycle, effective descent or an unconditional
quasi-split inner form.
