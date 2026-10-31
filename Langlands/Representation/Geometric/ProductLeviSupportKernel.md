# Restriction and the kernel of the product Levi quotient

This internal construction develops the kernel of the natural map
`productLeviQuotientMap` from `ProductLeviClosedQuotient`. Let `Q` and `S` be
refinements of a coarse block shape `B`. All representations are smooth complex
representations over an actual finite p-adic extension, with independent field
and coefficient universes. No admissibility, dimension or length hypothesis is
imposed.

## Raw restriction and normalization

`productLeviRestrictionMap T B Q A` sends a flattened induced function `f` to
the value at the outer identity of its image under
`flattenedInductionInStagesIso`. Its target is the actual normalized induced
representation inside `B.Levi`, with the coefficient representation pulled back
along the inverse flattened Levi equivalence. It is a linear map between these
actual function spaces.

The inverse comparison formula `flattenedInductionInStagesIso_inv_eval` follows
by composing the two published function-preserving comparison specifications.
The forward formula `flattenedInductionInStagesIso_hom_eval` follows from that
inverse formula and the normalized covariance under the coarse block diagonal
section. It says that evaluation of the inner function at `m` is
`half_B(m)⁻¹` times evaluation of `f` at `leviEmbedding(m) * g`.

Restriction is surjective: choose a smooth outer induced function having any
specified value at the identity using the existing smooth evaluation theorem,
then pull that function back through the stages isomorphism.

## Radical relations

`flattenedUnipotentProjection` is the actual coarse Levi projection restricted
to the flattened upper radical. The published equality of that radical with
`composedUnipotent` makes its codomain the inner upper radical. The restricted
block diagonal section proves surjectivity.

`productLeviRestrictionMap_unipotent` proves compatibility of restriction with
these radical actions. Equivariance of induction in stages first moves a
translation through the comparison. Coarse parabolic covariance then expresses
identity evaluation using the coarse projection. The coarse half modulus is
one on the inner radical, giving precisely the inner radical action.

Consequently `productLeviRestrictionMap_relations` proves that restriction maps
the entire flattened radical relation submodule onto the inner one. For one
containment, each generating difference maps to its corresponding inner
difference. For the reverse containment, lift both the inner radical element
and the coefficient vector through the two surjective maps.

## Kernels

`productLeviQuotientMap_mk` records that the existing normalized natural quotient
sends `[f]` to the inner class of the restriction of `f`.
`productLeviQuotientMap_ker` identifies its component kernel with the image,
under the actual flattened Jacquet projection, of the raw restriction kernel.
For a class in the quotient kernel, lift the relation represented by its
restriction to a source relation `z`. Then `f-z` has zero restriction and the
same source Jacquet class as `f`. The converse follows immediately from the
representative formula. The published `jacquetModuleEquiv` compares the
parabolic-radical quotient convention with the ambient radical convention used
for lifting relations.

`productLeviRestrictionMap_eq_zero_iff` identifies the raw kernel exactly with
functions vanishing at every element of the coarse parabolic. One direction
uses coarse covariance and the inverse evaluation formula. The other uses the
forward formula at every inner Levi element and pointwise extensionality.

## Provenance and scope

These are internal consequences of the existing normalized induction-in-stages
comparison, actual radical comparison, triviality of the outer half modulus on
the inner radical, and elementary linear quotient algebra. No additional
source-backed statement or choice of geometric-lemma filtration is introduced.
The identification of the vanishing subspace with an initial support-filtration
step, a compatible orbit ordering with the coarse closed subset last, and the
final product-Levi geometric lemma remain separate obligations.
