# Actual adelic determinant growth on a real-place slice

This internal supporting result towards `RealPlaceFunctionalEquationStatement` proves
`Langlands.Global.RankinSelbergGlobal.RealPlaceDeterminantGrowthStatement.{u}`.
It supplies the height estimate needed when specializing a global
determinant-power bound to an actual real-place restriction.

The statement quantifies over every number field `F`, positive matrix
size `n`, real place `w`, finite adelic point `b`, and real exponent `β`.
It asserts the existence of a nonnegative real `C` and natural `N` such
that for every `g ∈ GL_n(ℝ)`,

```text
detNorm F n (realPlacePoint F n w g * finitePoint F n b) ^ β
  ≤ C * realMatrixHeight g ^ N.
```

There is no compact-adele-quotient hypothesis in this supporting result.
The proof retains the free number-field universe `u`.

The key exact normalization calculation is
`RealPlaceRestriction.detNorm_realPlacePoint`:
the actual normalized adelic determinant norm of the inserted real
matrix is `|det g|`. The proof projects the determinant in mixed
coordinates to every real and complex place, using naturality of the
matrix determinant. At `w` it is the determinant of `g`; at all other
places it is one. The real and complex completion equivalences preserve
norms. In the normalized product of infinite-place norms only `w`
contributes, with multiplicity one because it is real. The finite
component is identity and contributes one. This uses the existing
actual determinant norm and its split formula.

`exists_detNorm_rpow_le_realMatrixHeight` now combines the preceding
module's bound for `|det g|^β` with multiplicativity of the actual
adelic determinant norm. The fixed finite point contributes the positive
constant `detNorm F n (finitePoint F n b)^β`, which is absorbed into `C`.
`realPlaceDeterminantGrowth` packages this proof as the statement.

This is a growth estimate for the determinant factor. It does not itself
prove a Whittaker coefficient bound, smoothness or a functional equation.
The height definition comes from the earlier internal coefficient-space
construction, whose organization follows the complex-place
model. The determinant calculations and height estimates here are internal
proofs from the existing Library definitions.
