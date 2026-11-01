# Actual bi-smooth realization on the uniform principal box

This internal derived prerequisite adapts the pointwise realization argument in
`RankOneMatrixFunctionalEquationComparisonBoxCoefficient` and
`RankOneMatrixFunctionalEquationComparisonBoxConvergence` to the uniform box of
`RankOneMatrixFunctionalEquationComparisonUniformBox`. No additional analytic or
representation-theoretic hypothesis is introduced.

For every original vector `w` of the Whittaker coefficient model of a smooth
representation of GL_(m+2), `exists_principalModelRealization` chooses a positive
principal level `a`, a compact open left-averaging subgroup `K`, and the actual
normalized bi-smooth matrix coefficient `averagedModelCoefficient` on that same
model representation. With `c` the additive conductor, its definition
`PrincipalModelRealization` records all of the following: `c+a ≥ 0`; `w` is fixed
on the right by the principal level and its determinant-rank-one image; `K`
fixes the full matrix test `boxLatticeTest F (c+a) c a` and has determinant norm
one; the actual coefficient equals the original function pointwise on this
exact box; and it retains the original function's right principal invariance
globally. The field and representation universes are independent.

The determinant reduction lemma is the published box-coefficient argument
with the incidental bounds on `q` and `A` replaced by `q ≤ A`. UniformBox's
proved multiplication equivalence supplies precisely that generality. For
the chosen uniform box, the first-row condition is automatic from principal
congruence, and the character is trivial on the conductor lattice. A principal
level contained in the original vector's open stabilizer and its continuous
determinant pullback is deepened to ensure `c+a ≥ 0`. The final compact left
subgroup lies in the full test stabilizer and the same determinant pullback.
Both a box point and its left translate therefore reduce to the same
model value at the determinant diagonal. Normalized left integration gives
pointwise equality. Associativity and the original right stabilizer prove
right invariance of the actual coefficient.

The coefficient is not asserted to equal `w` globally. No Fourier endpoint,
convergence outside the box, scalar integral equality, or functional equation
is asserted here. Those require separate extraction and comparison arguments.
