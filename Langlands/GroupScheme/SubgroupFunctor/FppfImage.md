# Fppf images and full inverse images of represented subgroup functors

Worker 1372.

This is derived infrastructure over any base scheme `B : Scheme.{u}`. It uses
the published actual subgroup functors, group-scheme kernel, and effective
epimorphism descent for represented monic subgroups. It invokes no external
structural theorem.

`SubgroupFunctor.IsFppfImage F E q` says that there are monic group-scheme
representatives `i : H ⟶ G` of `F` and `j : K ⟶ Q` of `E`, and an actual
homomorphism `p : H ⟶ K` with `i ≫ q = p ≫ j`, whose scheme morphism is flat,
surjective and locally of finite presentation. It is an existence predicate;
it does not construct representatives. No closedness, smoothness, affineness,
connectedness, field or normality assumption is included. Surjectivity refers
to the underlying scheme morphism. It does not assert that every point of `E`
lifts over its original test scheme.

`IsFppfImage.map_le` proves ordinary image containment on all tests from the
commuting square. `IsFppfImage.comap_eq_of_kernel_le` says that `F` is the full
inverse image of `E` under `q` if `F` contains the range of the actual kernel
inclusion `kernelι q`. The entire scheme-theoretic kernel is used, including
its points on nonreduced test schemes; no smoothness of that kernel is needed.

For the nontrivial containment, let `x` map into `E` on a test scheme `T`.
Represent its quotient image by a point `y` of `K`, and pull back `p` along
`y`. The resulting fppf cover `a : V ⟶ T` has a lift `z` in `H`. The right
difference of `a ≫ x` and the image of `z` is killed by `q`, hence lies in `F`
by the kernel-containment premise. Since the image of `z` also lies in `F`,
so does `a ≫ x`. The published `mem_range_of_comp_mem_range` descends this
membership to `T`, using monicity of the representative and Mathlib's fppf
effective-epimorphism theorem. The cover need not be quasi-compact. The reverse
containment is `map_le` rewritten by the image/inverse-image adjunction.

For a commuting square `j ≫ q = p ≫ j'`,
`comap_eq_of_quotient_square` transports `F'.comap j' = E'` to `F.comap j = E`
when `F = F'.comap q` and `E = E'.comap p` are already known.
`comap_eq_of_fppfImage_quotient_square` supplies these two identities from
actual fppf-image predicates and containment of the full two kernels. Both are
equalities of subgroup functors on every test scheme.

These lemmas can be used in centre or radical quotient arguments once their
fppf-image and kernel-containment premises have been proved. They do not prove
those structural premises for semigroup subgroups, construct the quotients, or
establish any case of `SemigroupComparisonStatement` on their own.
