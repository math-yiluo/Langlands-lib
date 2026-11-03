# Trivial factors in represented fppf-local subgroup products

Author: Worker 1473.

This internal prerequisite defines `SubgroupFunctor.IsFppfSaturated` and
proves elementary consequences of the published `FppfLocallyInProduct`
and `IsFppfProduct` definitions. It works over an
arbitrary base scheme, with arbitrary relative scheme tests. It does not
assert representability or the existence of a unipotent radical.

`IsFppfSaturated F` means that membership in `F` can be checked after one
flat surjective morphism of test schemes locally of finite presentation.
A subgroup represented by a monomorphism satisfies this property:
the published `mem_range_of_comp_mem_range` descends the factorization,
because the covering map is an effective epimorphism. No quasi-compactness
assumption on the cover is needed. For any functor satisfying this property,
the laws `right_bot_iff` and `left_bot_iff` eliminate a trivial right or
left factor from local product membership.

If `i : H ⟶ G` is a monomorphism of group schemes, a point belongs
fppf-locally to `range i` times the trivial subgroup if and only if it belongs
to `range i` on the original test scheme. The same holds with the trivial
factor on the left. The hypothesis is on `i.hom.hom`, the morphism in the
category of schemes over the base.

The product proof unpacks the supplied fppf factorization. The point in the trivial
factor is the identity, so the restriction of the original point factors
through `i`. A flat surjective morphism locally of finite presentation is an
effective epimorphism, by Mathlib's `AlgebraicGeometry.Sites.Fpqc` instance.
The saturation property then descends membership through the cover.
Conversely, an existing factorization gives the
required local product using the identity cover.

Consequently, a closed subgroup represents its own fppf product with the
trivial subgroup, in either order. More generally, if one factor of a
represented fppf product is trivial and the other is represented by a
monomorphism, the product's all-test image equals that other factor.
The latter laws use the preceding membership equivalences on every test.
These are derived interface laws, rather than translations of an external
structural theorem.
