# Uniform restriction fibres as joins of two scaled depth subgroups

This internal construction is derived from the published multiplier-scaled
restriction subgroups and the root-multiple bound for a relative root system.
It makes no additional claim attributed directly to original literature.

The same-field constructions use an affine group scheme `G` over a field,
commutative group schemes `S` and `T`, a map `j : T.toGrp ⟶ G` whose underlying
scheme map is monomorphic, and a supplied root-datum valuation for `j`.
The intersection and product lemmas additionally assume that `G` is smooth.
The compatible field-extension equality uses a smooth affine group over the
lower field and its scalar extension as the upper ambient group.

`torusRestrictedRootDepthBlock` is the subgroup join of the scaled restriction
subgroup for a character `a` and that for `2a`, at the same real lower depth.
This definition is over one field and requires only the supplied valuation.

At depth zero, scaling any generator's depth by its positive restriction
multiplier leaves the depth unchanged. Comparing the two indexed suprema gives
equality of the scaled and uniform fibre subgroups for every character, without
any root-system hypothesis.

At nonnegative depth, the scaled subgroup and the block both lie in the uniform
fibre subgroup. For each generator, its positive multiplier is at least one,
so filtration antitonicity applies. A root in the fibre of `2a` also lies in the
fibre of `a`, with twice the multiplier.

In the compatible torus-then-field setting, suppose `a` is an actual lower root,
the lower torus is split, and its roots satisfy `HasRelativeRootSystem`.
Every upper restriction multiplier reflects to an actual lower root multiple.
The root-system bound forces that multiplier to be one or two. The corresponding
upper filtration at uniform depth therefore occurs in the scaled subgroup for
`a`, or in that for `2a` with multiplier one. This proves that the uniform fibre
subgroup equals the block at every nonnegative depth.

The same-field product lemma assumes that both tori are split, the character
is nonzero, and no third or higher positive multiple is an actual root for the
lower composite torus inclusion. The published doubled-root centrality theorem
then applies to these lower root groups. Each scaled subgroup lies in its
corresponding root group, so the two factors commute elementwise.
Centralization implies normalization, and the carrier of the subgroup join is
the set product of the carriers. This product description holds at every real
depth; no depth inequality is used in this step. In the compatible field setting,
the higher-root exclusion follows from the relative root-system bound and
field root comparison; that specialization is not separately packaged here.

For split upper and lower tori, supplied opposite factor pairs, and a nonzero
lower character `a`, the intersection of the scaled `a` and `2a` subgroups at
nonnegative depth `r` is the scaled `2a` subgroup at depth `2r`.
The published doubled-depth intersection
formula identifies the intersection with the whole doubled root group.
Filtration antitonicity, using `r ≤ 2r`, then yields the stated smaller
intersection.

The equality concerns subgroups of points over the extension field. It does
not descend either factor of a product to the original field and does not
establish the multipliable-root block-descent field of the unramified comparison.
