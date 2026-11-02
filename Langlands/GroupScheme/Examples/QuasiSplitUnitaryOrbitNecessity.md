# Necessary matrix conditions for hyperbolic unitary dynamics

Worker 37 adapts the scalar Laurent-polynomial argument of the published
`Dynamic.GeneralLinearOrbit` to the unitary matrix coefficients. The fields,
quadratic extension, basis of the matrix algebra and automorphism have the
conventions of `QuasiSplitUnitaryDynamic`. An auxiliary basis `v` of `E` over
`F` expresses each entry of `E ⊗[F] R` by scalar coefficients in `R`. The
basis need not be indexed by a finite type in this argument. All integral
weights `m` are allowed, including zero. No characteristic restriction is used.

`entryCoeff_lift_orbit` proves that each scalar coefficient of matrix entry
`(i,j)` in the conjugation orbit scales by the difference of the two integral
weights. It uses the explicit diagonal cocharacter and the linearity and
naturality of the tensor-coordinate map from
`QuasiSplitUnitaryTensorCoordinates`.

Over `Spec A`, evaluate a proposed orbit extension on `Spec A[X]`. The generic
invertible coordinate on `Spec A[T,T⁻¹]` gives
`toLaurent P = C(a) * T^(weights m i - weights m j)` for each scalar
coefficient. This is `toLaurent_polyPoint_entryCoeff`. If the difference is
negative, multiplying by the opposite positive power and comparing constant
coefficients shows `a = 0`. For a constant orbit, comparing Laurent monomials
shows that every coefficient with a nonzero weight difference vanishes. When
the weight difference is zero, injectivity of `Polynomial.toLaurent` makes
`P` constant, so evaluating at zero retains the original coefficient.

Finally, restrict to the affine open cover of an arbitrary test scheme.
Naturality restricts both subgroup membership and scalar coefficients.
Equality of global sections on that cover, followed by injectivity of the
basis coordinate map, yields the three necessary matrix conditions:
`matrixCoordinates_mem_blockParabolic_of_mem_parabolic`,
`matrixCoordinates_mem_blockLevi_of_mem_centralizer`, and
`matrixCoordinates_mem_blockUnipotent_of_mem_unipotent`. In the last case,
negative-weight entries vanish by the parabolic result, and zero-weight
entries equal those of the identity because the extension has identity zero
value. This includes nonaffine and nonreduced test schemes.

This is derived proof infrastructure for `QuasiSplitUnitary.DynamicStatement`.
The scalar argument is reused from the published `GeneralLinearOrbit` module,
and the unitary scalar-coordinate adapter and diagonal point formula are
Worker 1225's accompanying development. The source framework is the one cited
by `QuasiSplitUnitaryDynamicStatement.md`: Milne, *Algebraic Groups* (2017),
Example 13.31 and Theorem 13.33, printed pp.264–266, for dynamic subgroups, and
Proposition 24.40 and Definition 24.42, printed p.523, for unitary algebras with
involution. The explicit unitary identification is a derived calculation,
not an assertion that Milne's special linear example proves it verbatim.
