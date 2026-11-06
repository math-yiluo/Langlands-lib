# Actual centralizer translations realized by reflection products

This internal construction works with the supplied `ValuationBuildingData B`
over an arbitrary-universe nonarchimedean local field. It uses the actual
centralizer, normalizer, reduced apartment and opposite-pair representatives.

`reducedCentralizerTranslation` projects the existing translation homomorphism
to the quotient by the common root annihilator. Its image, viewed as an
additive subgroup, is `centralizerTranslationLattice`. The subgroup
`reflectionTranslationLattice` is the image of those actual centralizer points
whose normalizer images belong to `reflectionNormalizer`. These names refer
to additive subgroups; their definitions impose no freeness or discreteness
condition.

Equality of reduced translations is equivalent to equality of the centralizer
actions, by full V6 and cancellation in the apartment torsor. The apartment
action kernel lies in the actual centralizer by the existing
`mem_centralizerPoints_of_normalizerAffineEquiv_eq_one`. Consequently, a
centralizer point belongs to the join of the reflection subgroup and action
kernel exactly when its reduced translation belongs to the reflection
translation lattice. For the forward implication, factor the point as a
reflection product times an action-kernel point; the first factor must also
centralize the torus. Lift it to the represented centralizer and compare
translations. Conversely, equal translations give equal actions, so the
quotient of the two normalizer points lies in the action kernel.

For two actual opposite-pair representatives along the same relative root,
their integral coroots agree by `reflectionPair_coroot_eq`. The product of
the inverse of the first representative with the second has a centralizer
lift. Composing their two affine-reflection formulas shows that its reduced
translation is the difference of their root values times the common reduced
coroot. This proves membership of each such vector in
`reflectionTranslationLattice`, with no global opposite-pair-existence
premise.

`reflectionRelativeWeylMap` is the quotient projection to the actual finite
relative Weyl group, restricted to `reflectionNormalizer`. Under actual
opposite-pair existence and `HasRelativeRootSystem B.i`, this map is
surjective. For each root the proof chooses a nonidentity actual root point
and an opposite pair. Their normalizing product belongs to the reflection
subgroup, negates the root and centralizes its full character kernel. The
existing integral-reflection constructor assembles these products into
`RelativeRootReflectionData`. Its finite-Weyl generation theorem, with the
explicit actual-root-system premise, puts every quotient class in the image
of the restricted projection. No full apartment axioms enter this argument.

Surjectivity of that map factors each actual normalizer point as a reflection
product followed by an actual represented centralizer point. The proof lifts
the quotient equality using `QuotientGroup.eq` and
`exists_centralizer_lift`. Under this surjectivity premise,
`reflections_sup_ker_eq_top_iff_translationLattice_eq` proves the equivalence
between full normalizer generation modulo the apartment-action kernel and
`reflectionTranslationLattice = centralizerTranslationLattice`. Forward,
every centralizer point belongs to the full join and the earlier membership
criterion applies. Reverse, factor any normalizer point as above; equality
of the lattices places its centralizer factor in the join by that same
criterion. The corollary
`reflections_sup_ker_eq_top_iff_translationLattice_eq_of_oppositePairs`
supplies finite-Weyl surjectivity from the two hypotheses just described.

Finally, `normalizer_facet_fixing_of_translationLattice_eq` retains explicit
opposite-pair existence, finite-Weyl surjectivity and equality of the actual
translation lattices. Those premises put every normalizer point in the
reflection subgroup joined with the action kernel. The previously proved
actual-data local-finiteness and facet theorem then shows that an actual
normalizer point preserving a full facet setwise fixes it pointwise. Its
facet and action are the existing sign-class facet and supplied apartment
action; there is no change of facet convention.

This unit does not assert that every actual centralizer translation lies in
the reflection translation lattice. It does not prove opposite-pair
existence, the full actual relative-root-system predicate, simply connected
normalizer generation or
`SimplyConnectedFacetFixingStatement`. Its provenance is the direct
composition of the existing actual centralizer and reflection constructions
with elementary subgroup and affine-torsor calculations.
