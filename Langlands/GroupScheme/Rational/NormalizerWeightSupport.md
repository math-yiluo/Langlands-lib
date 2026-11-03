# Normalizer permutations of actual tangent weights

This derived module constructs a permutation action on the actual tangent-weight
support of a subgroup functor normalized on all tests. It is an intermediate
step toward the Weyl-stability argument in Borel–Tits 1965, Proposition 3.6;
it does not establish that proposition or the minimal-parabolic Levi-centralizer
theorem.

The data are an arbitrary field `k`, an affine group scheme `G`, any group
scheme `H`, a morphism `j : H → G`, and an all-test subgroup functor `F` of `G`
stable under conjugation along `j`. A commutative group scheme `T` maps to `H`
by `t`, whose underlying scheme morphism is monic. No splitness, smoothness,
reductivity, maximality, finite Weyl group, or geometric structural theorem is
assumed.

The support is `actionWeightSupport (conjugation (t ≫ j)) F`: a character occurs
when its actual adjoint weight space contains a nonzero vector whose dual-number
point lies in `F`. The zero character is included if it occurs.

`basePointAdjoint_mem_tangentSubmodule` applies the all-test stability hypothesis
at the dual-number test scheme. Naturality of constant points identifies this
conjugation with the adjoint of a ground-field point of `H` mapped into `G`.
Thus it preserves the intrinsic tangent submodule of `F`.

`weylAction_mapsTo_actionWeightSupport` takes a nonzero weight vector in that
submodule. The existing normalizing-point identity transports along `j` and
sends its adjoint to the Weyl-transformed weight space. The preceding lemma
preserves membership in the tangent submodule. Invertibility of the adjoint
preserves nonzeroness. Applying the same construction to the inverse normalizing
point gives `weylAction_mem_actionWeightSupport_iff`.

Every element of the existing quotient `relativeWeylGroup t = N_H(T)(k)/Z_H(T)(k)`
has a normalizer representative. Hence the proved support invariance descends
to its existing full-character action, as expressed by
`relativeWeylCharacterAction_mem_actionWeightSupport_iff`.
`normalizedWeightPermutation` restricts that action to the support subtype;
its inverse is the restriction of the inverse quotient element. The group
homomorphism laws follow from those of the full-character action.
`normalizedWeightPermutation_apply` identifies the underlying character exactly.

The construction is derived from the published actual tangent submodule,
conjugation weight comparison, normalizing-point weight transport, and quotient
character action. No abstract replacement for the subgroup or its weights is
introduced. Geometric root-system realization, positive-root containment,
Galois stability, and the main ambient centralizer theorem remain separate
obligations.
