# Descent of ordered products through a central extension

This internal module develops the final fppf descent step in the proof of CGP
Theorem 3.3.11, *Pseudo-reductive Groups*, second edition (2015), printed
pp.115–116 (PDF pp.141–142), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. It uses actual group schemes,
their actual kernels, finite products and ordered multiplication over an
arbitrary base scheme.

`kernelFamilyPointsEquiv` identifies tuples of points of the actual factor
kernels with tuples whose factor quotient images are the identity. This is
the product of the Library's canonical kernel point equivalences. Its
projection formulas identify the forward and inverse coordinates with the
actual kernel inclusions.

`kernel_coordinates_unique` and `kernel_coordinates_exist` assume an
isomorphism for ordered multiplication in the kernels. A family of maps from
the factor kernels to the ambient kernel must commute with the original
factor maps and the kernel inclusions. Evaluating this square identifies
the included kernel product with the original ordered point product.
Bijectivity of the actual kernel product then gives uniqueness and
existence of kernel corrections.

`isIso_orderedMultiplication_of_centralExtension` considers a commuting
diagram of group-scheme homomorphisms from each original factor to its
quotient factor and from the ambient group to its quotient. It assumes that
the factor quotient maps are flat, surjective and locally of finite
presentation, that the ambient kernel is central on every test scheme,
and that ordered multiplication is an actual scheme isomorphism for both
the quotient factors and the kernel factors. It concludes that the
original ordered multiplication is a scheme isomorphism.

For uniqueness, quotient coordinates agree, their componentwise differences
are in the factor kernels, and centrality reduces equality to uniqueness
of kernel factorization. This proves that the original scheme map is a
monomorphism. For local existence, evaluate at the ambient group itself and
factor the quotient image of its identity test point. A succession of
pullbacks lifts the finite quotient-coordinate family over one fppf cover.
Kernel factorization corrects the product of those lifts to the given
point over that cover. The cover therefore factors through the original
monomorphism. An fppf cover is an effective epimorphism, so the
effective-cover factorization criterion makes that monomorphism an
isomorphism. The argument includes an empty family and assumes no lifting
of quotient points on the original test scheme.

This is a conditional geometric lemma. It supplies no central subgroup,
quotient, semigroup realization, compatibility of semigroup subgroups with
quotients or intersections, or vector-group decomposition. Those geometric
inputs and the exact cross-exclusion consequences are still required for
the full published `SemigroupOrderedProductStatement`. The generic
categorical route is derived from the actual Library constructions and
Mathlib's effective-epimorphism theory. Worker 362 implemented the imported
point coordinates and product-map criteria from the initial point formula
draft shared by Worker 1313.
