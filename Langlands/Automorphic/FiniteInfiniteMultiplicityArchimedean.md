# Admissible compact and local Lie structures on finite-factor multiplicities

This internal construction for Task 7294 equips finite-factor multiplicities
with their actual compact and Lie actions at each infinite place. It proves
the genuine local `(g,K)` axioms and admissibility for the full archimedean
compact action. It constructs no inverse-transpose pairing and does not
assert irreducibility of a restriction to a single place.

For a supplied actual finite factor `A`, evaluation at a nonzero vector
`a` is injective on the multiplicity space when `A` is irreducible. Choose
an open finite subgroup fixing `a`. Evaluation embeds the intertwiners from
any finite-dimensional compact representation into the corresponding joint
multiplicity space of the original realization: finite equivariance makes
their values fixed by the subgroup, and compact equivariance is preserved
under evaluation. Joint admissibility of the original realization thus
makes this compact-intertwiner space finite-dimensional. This proves the
Library predicate `IsAdmissibleGKModule` for the whole archimedean compact
group. The published theorem `CuspidalOperatorRealization.isJointlyAdmissible`
supplies the joint-admissibility premise for every cuspidal realization,
without a central-character assumption.

At each real or complex place, the compact action is restriction along the
existing compact-place inclusion and the Lie action is restriction along
the genuine complexified Lie-place inclusion. The complex-place domain
complexifies the entire underlying real matrix Lie algebra.

Evaluation at a nonzero finite-factor vector intertwines both restricted
actions and is injective. The local `(g,K)` axioms therefore transfer from
the existing actual realization. Compact finiteness is reflected by the
injective compact intertwiner. Every linear functional on the multiplicity
space extends across the injection to one on the original realization, so
the published continuity and differentiation statements hold against every
such functional. Finally, injectivity reflects the actual compact/Lie
adjoint covariance. The proof implements this transfer separately for the
real and complex predicates, retaining their exact matrix-curve
derivatives.
