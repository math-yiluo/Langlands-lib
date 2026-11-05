# Power comparison for actual rational-point matrix norms

The theorem `Langlands.Plancherel.rationalMatrixNormComparison.{u}` proves the
whole proposition `RationalMatrixNormComparisonStatement.{u}`. The source
representation is a supplied closed embedding of any group scheme over a
nonarchimedean local field. The target is any algebraic matrix representation
of the same group scheme. Both finite matrix index types are nonempty. The
constant and natural exponent are chosen before every actual rational point.
There is no connectedness, reductivity, characteristic or splitness premise.
The norm is the exact residue-normalized `rationalMatrixNorm` in the assigned
coefficient-growth target. The comparison is an internal prerequisite and
supplies no coefficient estimate or rational-group decomposition by itself.

The implementation has four steps.

1. `polynomial_evaluation_power_bound` proves that a polynomial over any normed
   field is bounded by `c * t ^ d`, with `c > 0`, whenever `t ≥ 1` bounds all
   its variable norms. Polynomial induction treats constants, sums, and
   multiplication by a variable. Sums use the sum of the two exponents so that
   both original powers are bounded by the new power. The coefficient field
   and the variable index type have independent universes.
2. `rationalMatrix_eq_affineMatrix` identifies the identity-test matrix with
   the affine-test matrix under `rationalPointEquiv`. It compares entries using
   `rationalMatrix_apply_apply`,
   `GeneralLinear.affinePointsEquiv_entry_evaluation`, and
   `rationalPointEquiv_left`.
3. `exists_polynomial_regularFunction` lifts a global regular function through
   `IsClosedImmersion.isAffine_surjective_of_isAffine`, then lifts its
   general-linear coordinate-ring class through `Ideal.Quotient.mk_surjective`.
   Evaluation at an actual rational point is evaluation of that polynomial on
   its matrix and inverse entries. The equality follows from the affine point
   equivalence, `GeneralLinear.affinePointEvaluation_map_classify`, and
   `GeneralLinear.classify_quotient`. This proves the polynomial identity for
   every actual point; it does not assume a chosen affine presentation of the
   original group.
4. `regularFunction_rationalMatrixNorm_bound` applies the polynomial estimate
   with the residue-normalized absolute value. The bound on variables is given
   by `HarishChandraSchwartz.norm_le_glNorm` and `norm_inv_le_glNorm`, and the
   common real bound is at least one by `one_le_rationalMatrixNorm`.
   The final theorem applies this to the finitely many pullbacks of target
   entry sections. `Finite.exists_le` supplies a common exponent and constant.
   The constant is positive because it bounds one of the positive entry
   constants and the target index type is nonempty. Applying the same entry
   bounds at the inverse group point controls inverse entries, using
   `rationalMatrixNorm_inv`. `HarishChandraSchwartz.glNorm_le` then gives the
   desired matrix-norm bound.

The imported `RationalMatrixNormComparisonStatement` pair is the exact target;
`GeneralLinearPointTopology` provides the affine-coordinate evaluation
identities, and Mathlib's `Morphisms.ClosedImmersion` provides section
surjectivity. Other declaration dependencies named above are inherited from
these modules. The auxiliary normed-field structure is used only inside the
numerical estimate. The statement itself uses the canonical actual rational
point carrier and the original local-field assumptions.

All mathematical content in this proof file is an internal derivation from
these existing coordinate and elementary norm lemmas. No external theorem is
added as an assumption. The proof does not depend on the pending global
coefficient-growth proof or on finite length of an admissible representation.
