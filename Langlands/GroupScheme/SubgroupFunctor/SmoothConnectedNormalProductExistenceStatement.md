# Smooth connected represented products of normal closed subgroups

`Langlands.GroupScheme.SmoothConnectedNormalFppfProductExistenceStatement.{u}`
is an unproved proposition target over every field `k : Type u`. The ambient
group scheme `G` is affine and locally of finite type over `k`. The homomorphisms
`i : H ⟶ G` and `j : N ⟶ G` are closed immersions, their sources are smooth and
connected, and their images are normal in `G` on every relative scheme test.
No smoothness or connectedness of the ambient group is required.

The conclusion constructs an actual group scheme `P` and homomorphism
`p : P ⟶ G`. The existing predicate
`SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
(SubgroupFunctor.range j) p` requires `p` to be a closed immersion and identifies
its image with the ordered fppf-local product. Concretely, for every relative
scheme `T` and point `x : T ⟶ G.X`, membership in the image of `p` is equivalent
to the existence of a relative map `v : V ⟶ T` that is flat, surjective, and
locally of finite presentation, together with points of the two factor images
over `V` whose product is `v ≫ x`. This retains nonaffine and nonreduced tests
and does not require factorization on the original test. The conclusion also
requires `Smooth P.X.hom` and `ConnectedSpace P.X.left`.

The source is Milne, *Algebraic Groups* (2017), Theorem 5.82 and its proof,
printed pp.120–121 (PDF pp.136–137), together with Lemma 6.41 and its preceding
paragraph, printed p.134 (PDF p.150). Theorem 5.82 constructs `HN` as an
algebraic subgroup when `N` is normal, identifying it with the sheaf associated
to the ordered product of the represented subgroup functors. Lemma 6.41 gives
closure under products for properties preserved by quotients and extensions;
the preceding paragraph explicitly includes smoothness and connectedness.
Here both factors are assumed normal, as needed by the radical application.
The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The official errata snapshot of 2 November 2026 has been read; it lists no
correction to these passages.

The statement is a specialization of those results to affine ambient groups
and two normal factors, using the Library's all-test fppf product interface.
It is not a verbatim formulation in Milne: the existing `IsFppfProduct`
Markdown explains the single-cover formulation of the sheaf image. Affineness
and local finite type of `G` imply finite type here; closed subgroup sources
are affine as well. The field is not assumed perfect or algebraically closed,
and no restriction on its characteristic is imposed.

This geometric prerequisite contains no unipotence premise or conclusion.
Normality of a supplied product follows separately from the two factor
normality hypotheses and the membership formula. Product unipotence, candidate
greatestness, and the exact `UnipotentRadicalExistenceStatement` remain
additional proof obligations. No theorem or instance proves this target here.
