# Actual affine unipotent quotients by field-extension descent

This derived internal construction combines the published smooth homogeneous
quotient existence theorem with `Chevalley.unipotentAffineQuotient`,
`HomogeneousQuotient.isAffine_of_fieldExtension`, and
`HomogeneousQuotient.exists_action_relativeDimension`. Worker 362 authored
this pair. The closed-orbit result and geometric unipotence are explicit
inputs, not assertions proved by this module.

Let `k` be any field and `K` any algebraically closed extension, with both
fields in an arbitrary common universe. The definition
`unipotentAffineQuotientOfFieldExtension` takes a smooth affine group scheme
`G` over `k`, a smooth closed subgroup inclusion `i : H ⟶ G`, and proofs that
both actual base changes `G_K` and `H_K` are unipotent in the Library's
representation-theoretic sense. It also takes the exact
`UnipotentAffineOrbitClosedStatement`.

First the general existence theorem supplies an actual smooth homogeneous
quotient `D` over `k`. Its quotient scheme is separated and of finite type,
its projection is smooth, surjective and quasi-compact, and its fibers on
every relative scheme test are precisely the right cosets of the specified
subgroup. Smoothness and affineness of `G`, smoothness of `H`, and the closed
immersion `i` survive base change. The conditional algebraically closed-field
construction therefore gives an affine homogeneous quotient over `K` for
the actual inclusion `i_K`. Comparison with `D.baseChange` and field-extension
affineness descent show that the original actual scheme of `D` is affine.
The returned `AffineHomogeneousQuotient i` keeps all of `D`'s original data.

`exists_unipotentNormalQuotientOfFieldExtension` applies this construction
when the original `G` is also connected and unipotent, the subgroup range is
normal and stable under a supplied actual automorphic action of any group
scheme `A`, and the source and subgroup have smooth relative dimensions
`d` and `n`, with `0 < n`. It retains the same closed-orbit and geometric
unipotence inputs. The normal homogeneous quotient adapter gives an actual
affine, smooth, connected unipotent group quotient `Q`, a homomorphism `q`,
and an actual descended action. Its represented fppf kernel equals the
specified subgroup range on every test scheme. The map `q` is smooth of
relative dimension `n`; `Q` has smooth relative dimension `m`, with
`d = n + m` and `m < d`. Equivariance holds on every relative scheme test.

These results do not prove preservation of unipotence under field extension,
unipotence of arbitrary closed subgroups, the closed-orbit proposition, or
the host ordered-product statement. No algebraic closedness of the original
field, splitness of the group, centrality of the subgroup, or special acting
torus is required by these conditional constructions.
