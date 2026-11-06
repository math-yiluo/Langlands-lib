# Comparing opposite cocharacters with the same centralizer

This is an internal, derived comparison using the published dynamic subgroup,
split-torus image, rational root-point, and root-sign results. Worker 1650
implements the argument. It does not supply a new structural root theorem.

`exists_common_maximalSplitTorus_of_range_le_centralizer` applies to any
affine group scheme locally of finite type over an arbitrary field. If the
image of the second cocharacter centralizes the first, their product defines
a homomorphism from the product of two multiplicative groups. Its actual
image is a split subtorus, and a maximal split extension of this image gives
the simultaneous factorization. Neither reductivity nor smoothness is used
in this step.

`CommonMaximalSplitTorusFactorization chi psi` packages the actual torus,
its inclusion, the two lattice cocharacters, maximal splitness, and the two
factorization equalities. The noncomputable definition
`commonMaximalSplitTorusFactorization` chooses this data using the preceding
existence theorem and the centralizing-range premise. The final comparison
uses this chosen factorization. The choice adds no uniqueness assertion for
the torus or its inclusion.

`not_both_positive_of_rational_parabolic_inf_eq_centralizer` applies to any
split-torus homomorphism into a smooth affine group over a field. An actual
root positive on both cocharacters would give a nonidentity rational point
in its actual root subgroup. The point lies in both dynamic unipotent
subgroups, hence in the two parabolics. The rational intersection hypothesis
places it in the first centralizer. Uniqueness of orbit extensions forces
a centralizer point contracted to the identity to be the identity, a
contradiction. This argument works over finite and imperfect fields and
does not assume density of rational points.

`opposite_root_signs_of_rational_parabolic_inf_eq_centralizer` additionally
assumes equality of the two centralizer functors and negation stability of
the actual root set. Published rational-point detection identifies the
zero-root supports. The preceding exclusion for a root and its negative
rules out both equal strict signs. These facts give the stated opposite
weak and strict sign equivalences.

`oppositeDynamicParabolicUniqueness_of_relativeRootNegation` proves the exact
published `OppositeDynamicParabolicUniquenessStatement` conditionally on
`RelativeRootNegationStatement`, at the original universe level. Equal
centralizers imply that the two cocharacters commute. The common maximal
split torus and the opposite-root sign equivalences then yield both
inclusions for the parabolics and for the unipotent subgroups, using the
published all-test root-sign criteria. The negated torus cocharacter
represents `Dynamic.oppositeCocharacter`.

The final implication retains the unconditional relative-root negation
statement as an explicit premise. This module alone does not prove the
unconditional opposite-parabolic uniqueness target. All other ingredients
in this comparison are imported as proved results; no root-system
realization is assumed implicitly.
