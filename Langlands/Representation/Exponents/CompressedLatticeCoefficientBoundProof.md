# Finite lattice coefficient bounds from compression spectra

Author: Worker 19.

`Langlands.compressedLatticeCoefficientBound` proves the complete
`CompressedLatticeCoefficientBoundStatement`. The argument stays on the
finite-dimensional space of vectors fixed by the supplied compact open
subgroup. All factorization and conjugation conditions remain explicit.

The internal helper `CompressedLatticeBound.exists_apply_le_prod` first
chooses a closed spectral radius strictly below the given bound for each
coordinate generator, using the generic published
`StrictCartanBound.exists_eigenvalue_bound_lt`. It takes an intermediate
positive radius and applies `EndomorphismBound.exists_endNorm_pow_le` to
bound all generator powers. The helper
`CompressedLatticeBound.endNorm_le_prod_of_pow_bounds` uses the finite
coordinate sum and multiplicativity to combine these power bounds, using
`EndomorphismBound.endNorm_mul_le`. Evaluation is bounded by
`EndomorphismBound.exists_apply_le_endNorm`. Enlarging the resulting constant
by one makes it positive, including when the fixed-vector space is zero or
the index type is empty.

For the actual representation, admissibility supplies finite dimension of
`K`-fixed vectors. `Jacquet.compressedAction_mul_of_factor` proves the required
multiplicativity from precisely the statement's displayed factorization and
conjugation hypotheses. Finally
`StrictCartanBound.dual_apply_eq_compressedAction` identifies the evaluation
of the compressed operator with the original coefficient because the dual
functional is fixed by `K`.

The two imported `StrictCartanBound` helpers have unrestricted group or
finite-dimensional linear-algebra scope despite being housed in a module
that also proves a GL theorem. This proof uses neither that GL theorem nor
any GL objects. It uses no classification, geometric lemma, adjointness,
character independence or cuspidal support input. Geometry, Jacquet spectra,
Haar volume comparison and the final square-integrability criterion remain
consumer obligations.
