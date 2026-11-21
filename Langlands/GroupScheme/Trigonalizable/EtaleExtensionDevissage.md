# Reduction from smooth unipotent kernels to vector groups

Author: Worker 3502 (Task 7944). Module
`Langlands.GroupScheme.Trigonalizable.EtaleExtensionDevissage`.

`EtaleExtensionSplit.exists_section_of_vector_splitting` fixes a group
scheme `H` affine over a perfect field. It assumes that every smooth
surjective homomorphism from an affine group to `H` whose full kernel is
a vector group has a group-scheme section. Under this assumption, it
splits `q : E ⟶ H` for `E` smooth affine, `q` smooth and surjective, and
`kernel q` connected and unipotent. Neither `E` nor `H` is required to be
connected.

The induction is on the relative dimension over the field of `K = kernel q`,
which is smooth by base change of `q`. If `K` is trivial, `q` is an
isomorphism. Otherwise `perfectFieldUnipotentSplit` gives splitness of `K`,
and `RelativeRoot.splitUnipotentStableVectorSubgroup`, applied to conjugation
by `E`, gives a positive-dimensional smooth closed vector subgroup `V` of
`K`. It is central in `K` and stable under the whole `E`-action, hence
normal in `E`. Form the smooth affine quotient `r : E ⟶ Q` by `V`.
Fpqc homomorphism descent factors `q` as `r ≫ q'`; `q'` is smooth and
surjective.

The restriction `K ⟶ kernel q'` is smooth and surjective. The private
`range_kernel_factored` lemma proves on every test scheme that its kernel
is the range of `V ⟶ K`, by testing both kernels under their monic
inclusions. Thus this restriction has relative dimension `dim V`. Its
target is connected and unipotent by surjectivity and flatness, and has
strictly smaller dimension than `K` by addition of relative dimensions.
We apply induction to `q'`. The resulting section `s : H ⟶ Q` is closed
because `q'` is separated. The pullback of `r` along `s` is therefore an
affine group with a smooth surjective map to `H` and with vector kernel
isomorphic to `V`. Apply the assumed vector splitting to this map, then
compose with the pullback inclusion into `E`.

This is an internal reduction for [the étale splitting proof](EtaleExtensionSplitProof.md).
It adapts the dimension induction of
[`CharacteristicZeroUnipotentExtension`](../Reductive/CharacteristicZeroUnipotentExtension.md)
and the vector subgroup and pullback step in
[`SplitUnipotentExtensionSection`](../Rational/SplitUnipotentExtensionSection.md).
For this application it replaces the characteristic-series reduction to
commutative kernels in SGA 3 XVII, Lemme 5.2.3 (see the
[statement's source discussion](EtaleExtensionSplitStatement.md)).
