# Point generation and normality in a commuting product

Worker 1636.

This internal helper module starts with two group-scheme homomorphisms
`j : H ⟶ G` and `i : K ⟶ G` over an arbitrary base. Their images commute on
every test scheme. The published `commutingSubgroupMultiplicationHom` is
assumed to be an isomorphism; no existence of a factor decomposition is
asserted here.

`commutingProductPointsEquiv` constructs a multiplicative equivalence from
the ambient point group to the product of the two factor point groups.
It postcomposes with the inverse multiplication and applies the published
`productPointsEquiv`; its inverse multiplies the two coordinates.

`exists_factor_points_of_isIso_commutingMultiplication` lifts an arbitrary
test-scheme point through the inverse multiplication and takes its two
product coordinates. Thus every point is a product of points in the two
factor images.

The two `SubgroupFunctor.IsNormal.range_comp` lemmas transport normality
from either factor to the ambient group. They write an ambient conjugating
point as a product of factor points. The other factor commutes with the
subgroup point, so its conjugation cancels; normality in the original factor
then supplies a point witnessing membership in the composite image.
Neither lemma requires the factor maps to be closed immersions.

`range_left_eq_bot_of_isIso_right_commutingMultiplication` proves that the
first range is trivial when the second factor map is itself an isomorphism.
Injectivity of multiplication compares the product points `(h,1)` and
`(1,i⁻¹j(h))`; their first coordinates give `h = 1`.

Over any commutative ring, the rational-point lemma proves that a subgroup
containing the images of both factors is the full rational-point group.
It applies the point decomposition and closure under multiplication.
These are direct categorical and group-theoretic consequences of the
existing product and commuting multiplication constructions, developed as
helpers for rational generation of simply connected groups. They use no
structural decomposition theorem.
