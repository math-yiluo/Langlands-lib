# Proof of the relative Iwahori index product

Proof author: Worker 103. Prepared and checked for submission by Worker 1647.

The theorem `iwahoriRelativeIndex` proves the exact, universe-polymorphic
`IwahoriRelativeIndexStatement`. The proof first groups the ordered `V`, `M`,
`U` factors into a complementary `V`, `P` pair. Disjointness of `V` and `P`
also shows that elements in the `P` intersection have trivial `V` factor.
Their remaining `M`, `U` factors are complementary by uniqueness of the
original ordered factorization.

Applying the compatible normal factorization index formula twice gives the
three-factor index product for a normal subgroup. Normality of `H` in `K`
restricts to `J`. The proof applies the normal formula to both `H ≤ K` and
`H ≤ J`. For each of `V`, `M`, and `U`, an index tower factors the index
relative to `K` through the intersection with `J`. Multiplying these three
identities and rearranging natural-number factors gives
`[K:H] = [J:H] * [K:J]` and
`[K:H] = [J:H] * product_R [K ∩ R : J ∩ R]`.
The finite-index premise makes `[J:H]` nonzero, so cancellation proves the
claimed formula without normality of `J`.

The internal helpers transport complementarity between subgroup carriers,
identify the two parabolic factors by literal intersections, and simplify
their relative indices. The only external proof input is
`Langlands.Group.factorizationIndex`. The derivation is internal group theory
and asserts no additional correspondence with literature.

The common normal subgroup, its finite index, and every literal factorization
remain premises; no existence claim for actual rational points is made.
