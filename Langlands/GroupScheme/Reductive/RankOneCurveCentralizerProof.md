# Regular quotient-curve bounds from connected reductivity

This internal assembly composes the published pseudo-reductive quotient-curve
construction with regular integral rank-one normalizer symmetrization and the
fixed-point sign embedding. It derives the signed unipotent data from connected
reductivity; it takes no normal-solvable-torus theorem as a premise. Provenance
is the composition of these named internal constructions. No new external
structural assertion is introduced.

The field `k : Type u` is algebraically closed, in arbitrary characteristic.
The ambient group `G` is connected reductive. The prescribed subgroup
`b : B ⟶ G` is closed, solvable and proper in the sense `¬ IsIso b`. A split
maximal torus factors as `t ≫ b`, and every pair of its actual roots is
integrally dependent. The rational normalizer point `n` has nonidentity class
in the actual relative Weyl quotient. The whole-torus centralizer is contained
in the range of `b` as subgroup functors, on every relative scheme test.

The projection `q : G.X ⟶ Q` is prescribed, smooth, surjective and
quasi-compact, with separated target. Its fibers satisfy the exact right-coset
law on every relative scheme test: `q(g) = q(h)` if and only if `g⁻¹ * h`
belongs to the range of `b`. Neither this quotient nor these hypotheses are
constructed here.

`regularSignedCurveUnipotentDataOfIsConnectedReductive` first applies
`regularRefinement` to the original cocharacter `ν` and subtracts its actual
normalizer translate. The dynamic centralizer of this generic symmetrized
cocharacter equals the whole-torus centralizer on every relative test. The
assumed containment and the curve bound `topologicalKrullDim Q.left ≤ 1`
therefore satisfy `signedCurveUnipotentDataOfPseudoReductive`; connected
reductivity supplies pseudo-reductivity. The result selects a sign and contains
an actual smooth connected affine unipotent representative of that signed
dynamic subgroup together with moving quotient-curve orbit data.

`positive_roots_eq_of_rankOne_curve_torusCentralizer_of_isConnectedReductive`
applies the published
`positive_roots_eq_of_rankOne_curve_quotient_of_isConnectedReductive` to the
regular refinement. Equality of the symmetrized dynamic centralizer with the
whole-torus centralizer supplies the required containment. The proof transports
original positivity by `regularRefinement_pos`, so its conclusion concerns
roots positive on the original, possibly nonregular cocharacter. Integral
symmetrization doubles root pairings; the proof divides by no integer and
imposes no characteristic restriction.

`positive_roots_eq_of_rankOne_quotient_three_fixedPoints_of_isConnectedReductive`
also assumes conjugacy of maximal tori inside `B` and the implication that
actual quotient dimension at least two gives an embedding of `Fin 3` into its
rational points fixed in the all-test sense. The subgroup-functor containment
restricts to rational centralizer containment. The rank-one sign embedding
maps fixed rational points into `Bool`, so it forces dimension at most one.
The preceding curve result then gives uniqueness of positive roots.

These are conditional helpers. Quotient existence, properness, centralizer
containment, the nonidentity normalizer class, torus conjugacy and the
three-fixed-point implication remain application obligations. In particular,
properness alone is not used to infer the fixed-point implication. This module
does not prove the final all-field positive-root uniqueness statement.
