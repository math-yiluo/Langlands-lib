# Root representatives from a kernel centralizer over a ring

This internal construction supplies part of the root-model argument for Task
5976. It works over any commutative ring `R` in the arbitrary universe `u`.
Its provenance is derived from existing Library constructions and proofs: the
actual semidirect product, closed affine identity-limit representatives,
`dynamicRingSmoothConnected`, and the all-test quotient-action comparison.
It asserts no additional result from the literature.

For an automorphic action `b` of `Gm` on a smooth affine group scheme `H`
over `Spec R`, `smooth_unipotentScheme_ring` and
`geometricallyConnected_unipotentScheme_ring` prove smoothness and
geometrically connected fibres of the existing actual
`AutomorphicAction.Affine.unipotentScheme b`. The proofs apply the unipotent
clause of `dynamicRingSmoothConnected` to the acting-factor cocharacter in
`H ⋊ Gm`. Its underlying scheme is the product of two smooth affine schemes.
The semidirect identity-limit representative is exactly the existing
representing scheme for the original action. Connectedness of `H` is not
needed, and these conclusions do not assume a dynamic connectedness statement.

Now let `S` be a commutative group scheme over `Spec R`, `i : S → G` a
homomorphism, and `a` an actual character of `S`. Supply an actual affine
scheme `C`, a homomorphism `j : C → G` representing the character-kernel
centralizer on every test scheme, and the quasi-compactness, flatness and
surjectivity of the character map `a : S → Gm`. These are explicit hypotheses;
this module does not construct the centralizer or prove these properties of
the character. No splitness hypothesis on `S` is used once they are supplied.

`RelativeRoot.Ring.subgroupScheme i a j hj` is the actual identity-limit scheme
of `quotientAction i a j hj`, the descended `Gm`-action on `C`.
`subgroupHom` composes its constructed inclusion into `C` with `j`.
If `j` is closed, `isRepresentedBy_subgroupHom` proves that this map represents
the full intrinsic root functor `RelativeRoot.subgroup i a` on every scheme
over the base. The proof rewrites that functor with
`quotientActionComparison` and composes the two representing inclusions.
`isClosedSubgroup_subgroupHom` composes their closed immersions. The scheme
is affine because the identity-limit construction is affine.

When `C` is smooth, `smooth_subgroupScheme` and
`geometricallyConnected_subgroupScheme` apply the ring-level identity-limit
results above. Thus a supplied smooth affine kernel centralizer with closed
inclusion and an fpqc character gives an actual smooth affine root
representative with geometrically connected fibres, without requiring
connectedness of `C` or `G`. The representation and affineness assertions do
not themselves require smoothness of `C`.

This module does not yet construct a kernel centralizer over the maximal
unramified integers, a split integral torus, an integral model with a specified
generic-fibre identification, or the equality between integral root points
and a valuation-filtration level. It also does not prove existence of the
models in `RootFiltrationModelData` or the target parahoric-model theorem.
Those construction and comparison steps remain separate obligations.
