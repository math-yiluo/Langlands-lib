# Closed normal inclusions on supplied adjoint quotients

Let `i : H ⟶ G` be an actual group-scheme homomorphism over any field, and
let `p : H ⟶ R` and `q : G ⟶ Q` be supplied actual adjoint quotients.
`IsAdjointQuotient.subgroupHom` constructs a homomorphism `R ⟶ Q`
provided that
`center H ≤ (center G).comap i`.
These are the full scheme-theoretic centre functors, tested on all schemes
and all their refinements. All declarations work in an arbitrary universe.

This is an internal construction using the published
`IsAdjointQuotient.desc`. The displayed containment makes `i ≫ q` kill
the full centre of `H`, so it descends through `p`. The proof of monicity
identifies this map with `SubgroupFunctor.quotientSubgroupHom` by the
uniqueness of the commuting square. The full kernel of each supplied
quotient is its source's full centre, making the displayed containment
exactly the kernel compatibility required there.
Flatness and scheme surjectivity are supplied by `IsAdjointQuotient`;
affineness of the connected reductive groups gives quasi-compactness.
`subgroupHom_square` proves `i ≫ q = p ≫ subgroupHom`, and
`subgroupHom_unique` proves uniqueness for that square.

If `i` is monic on the actual schemes over the field,
`subgroupHom_mono` proves the same for the induced map. The reverse
centre containment is the published `center_comap_le_of_mono`, so the
two kernels have exact inverse image. The generic quotient monicity lemma
then applies.

`subgroupHom_isClosedSubgroup` proves that this induced map is a closed
immersion. Its source is smooth, connected and affine; its target is affine
and locally of finite type. The companion `HomImageEmbedding` lemma makes
the flat surjective factor in its closed image factorization an isomorphism.
This argument does not require containment of the ambient centre in `H`.

`subgroupHom_isNormal` additionally assumes normality of the all-test range
of `i` and concludes normality of the all-test range of the constructed map.
It uses the companion `SubgroupFunctor.QuotientNormality` lemma, which
successively lifts quotient points through actual fpqc pullbacks and descends
membership in the monic range. It does not assume smoothness of the
quotients or their kernels.

Finally, `subgroupHom_isEquivariant` applies the adjoint action square
theorem: an equivariant `i` makes the constructed map equivariant for the
canonical actions on `R` and `Q`. No monicity premise is needed for this
compatibility assertion.

The centre-containment hypothesis is retained explicitly throughout.
This construction does not prove that hypothesis for a normal reductive
subgroup, construct the adjoint quotients, produce a normal-adjoint
retraction, or prove the semigroup intersection comparison.
