# Represented products with a normal closed subgroup

`Langlands.GroupScheme.NormalFactorFppfProductExistenceStatement.{u}` is an
unproved proposition target over every field `k : Type u`. The ambient group
scheme `G` is affine and locally of finite type over `k`. The homomorphisms
`i : H ⟶ G` and `j : N ⟶ G` are closed immersions, and the image of `j` is
normal in `G` on every relative scheme test. The image of `i` is not required
to be normal, and no smoothness or connectedness of `G`, `H` or `N` is
assumed.

The conclusion constructs an actual group scheme `P` and homomorphism
`p : P ⟶ G`. The existing predicate
`SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
(SubgroupFunctor.range j) p` requires `p` to be a closed immersion and
identifies its image with the ordered fppf-local product. Concretely, for every
relative scheme `T` and point `x : T ⟶ G.X`, membership in the image of `p` is
equivalent to the existence of a relative map `v : V ⟶ T` that is flat,
surjective, and locally of finite presentation, together with points of the
images of `i` and `j` over `V` whose product is `v ≫ x`. This retains
nonaffine and nonreduced tests and does not require factorization on the
original test. Nothing is claimed about smoothness or connectedness of `P`.

The source is Milne, *Algebraic Groups* (2017), Theorem 5.82 (isomorphism
theorem) and its proof, printed pp.120–121 (PDF pp.136–137). For algebraic
subgroups `H` and `N` of `G` with `N` normal, Theorem 5.82 states that `HN` is
an algebraic subgroup of `G`; the proof defines `HN` as the image of the
homomorphism `H ⋉ N → G` and identifies it with the sheaf associated to the
subfunctor `R ↦ H(R)N(R)` of `G`. The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The statement specializes the existence part of Theorem 5.82 to affine ambient
groups, using the Library's all-test fppf product interface; the remaining
assertions of Theorem 5.82 (about `H ∩ N` and the isomorphism
`H/(H ∩ N) → HN/N`) are not part of it. It is not a verbatim formulation in
Milne: the existing `IsFppfProduct` Markdown explains the single-cover
formulation of the sheaf image. Affineness and local finite type of `G` imply
finite type here, so `G` is an algebraic group in Milne's sense, and closed
subgroups of `G` are algebraic subgroups. The field is not assumed perfect or
algebraically closed, and no restriction on its characteristic is imposed.

This statement generalizes the published
`SmoothConnectedNormalFppfProductExistenceStatement`, which assumes both
factors smooth, connected and normal and additionally concludes that the
product is smooth and connected. The intended application takes for `i` the
dynamic subgroup `P_G(λ)` and for `j` a ground-field unipotent radical, as in
the product `P_G(λ)R_{u,k}(G)` of CGP Definition 2.2.1. No theorem or instance
proves this target here.
