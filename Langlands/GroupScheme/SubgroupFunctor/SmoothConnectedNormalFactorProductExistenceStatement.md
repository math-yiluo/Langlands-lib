# Smooth connected represented products with a normal second factor

`Langlands.GroupScheme.SmoothConnectedNormalFactorFppfProductExistenceStatement.{u}`
is an unproved proposition target over every field `k : Type u`. The ambient
group scheme `G` is affine and locally of finite type over `k`. The
homomorphisms `i : H ⟶ G` and `j : N ⟶ G` are closed immersions, and their
sources are smooth and connected. The image of `j` is normal in `G` on every
relative scheme test; the image of `i` is not required to be normal. No
smoothness or connectedness of the ambient group is required.

The conclusion constructs an actual group scheme `P` and homomorphism
`p : P ⟶ G`. The existing predicate
`SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
(SubgroupFunctor.range j) p` requires `p` to be a closed immersion and
identifies its image with the ordered fppf-local product. Concretely, for every
relative scheme `T` and point `x : T ⟶ G.X`, membership in the image of `p` is
equivalent to the existence of a relative map `v : V ⟶ T` that is flat,
surjective, and locally of finite presentation, together with points of the
images of `i` and `j` over `V` whose product, in this order, is `v ≫ x`. This
retains nonaffine and nonreduced tests and does not require factorization on
the original test. The conclusion also requires `Smooth P.X.hom` and
`ConnectedSpace P.X.left`.

The source is Milne, *Algebraic Groups* (2017), Theorem 5.82 and its proof,
printed pp.120–121 (PDF pp.136–137), together with Lemma 6.41 and its preceding
paragraph, printed p.134 (PDF p.150). For algebraic subgroups `H` and `N` of
`G` with `N` normal, Theorem 5.82 states that `HN` is an algebraic subgroup of
`G`; its proof defines `HN` as the image of the homomorphism `H ⋉ N → G` and
identifies it with the sheaf associated to the subfunctor `R ↦ H(R)N(R)` of
`G`. Lemma 6.41 states, for the same `H` and normal `N`, that `HN` has every
property `P` of `H` and `N` that is preserved by extensions and quotients; the
preceding paragraph names smoothness and connectedness as such properties.
The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The statement specializes the existence part of Theorem 5.82, together with
Lemma 6.41 for smoothness and connectedness, to affine ambient groups and
smooth connected factors, using the Library's all-test fppf product interface.
It is not a verbatim formulation in Milne: the existing `IsFppfProduct`
Markdown explains the single-cover formulation of the sheaf image. Affineness
and local finite type of `G` imply finite type here, so `G` is an algebraic
group in Milne's sense, and closed subgroups of `G` are algebraic subgroups.
The field is not assumed perfect or algebraically closed, and no restriction
on its characteristic is imposed.

Relation to published statements: this proposition generalizes
`SmoothConnectedNormalFppfProductExistenceStatement`, which additionally
assumes the image of `i` normal, and it is a special case of
`NormalFactorFppfProductExistenceStatement` strengthened by the smoothness
and connectedness of the product. The intended application takes for `i` the
smooth connected dynamic subgroup `P_G(λ)` of a smooth connected affine group
and for `j` its ground-field unipotent radical, as in the product
`P_G(λ)R_{u,k}(G)` of Conrad–Gabber–Prasad, Definition 2.2.1. No theorem or
instance proves this target here.
