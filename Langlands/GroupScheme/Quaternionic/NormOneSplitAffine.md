# Affine points under the split comparison of a quaternionic norm-one group

Module `Langlands.GroupScheme.Quaternionic.NormOneSplitAffine`, namespace
`Langlands.GroupScheme.Quaternionic`.

The module computes the matrices of points of norm-one isometry groups on affine tests in
two situations: the scalar group, and a quaternionic group transported to its split scalar
form by `NormOneSplit.splitIso`.

## Scalar groups

For a field `K`, a scalar form `q : (scalar K).QuadraticForms (Fin m)`
(`m ≠ 0`) and a commutative `K`-algebra `A`:

* `affineSectionsRingHom A` is the ring map from the global sections of the affine test
  scheme `Spec A` (as an object over `Spec K`) back to `A`, read from
  `Corepresented.affineSectionsIso`.
* `scalarMatrixPoint_normOne`: for an affine `A`-point `w` of the norm-one isometry group,
  the matrix `OrthogonalMatrix.scalarMatrixPoint q A (w ≫ ι)` of its image in the isometry
  group equals the test-scheme matrix `ScalarNormOnePoints.matrix q _ w` mapped entrywise by
  `affineSectionsRingHom A`.

  The proof writes both sides through the units of `A ⊗ M_m(K)`: the left side is the chart
  of the affine unit point (`OrthogonalMorita.coe_isometryAffineUnitsEquiv`), the right side
  is the matrix of the test-scheme unit point. The two unit points are related by
  `Corepresented.pointsEquiv_eq_affinePointsEquiv`, the matrix coordinates are natural
  (`ScalarMatrixCoordinates.matrixEquiv_naturality`), and the two comparison maps of
  `affineSectionsIso` compose to the identity.

## Quaternionic groups through the split comparison

Let `D` be a finite-dimensional central division algebra over a field `F` with a first-kind
involution `σ` whose symmetric subspace has dimension `3` (hypothesis `hσ`). Let
`q : σ.QuadraticForms (Fin m)` with `m ≠ 0`, `L` be a field over `F` and
`e : L ⊗ D ≃ M₂(L)` a splitting. `NormOneSplit.splitIso e σ q hσ`
identifies the base change to `L` of `σ.normOneIsometryGroup q` with the scalar norm-one group
of the split Gram form `NormOneSplit.gramQ e σ q` on `L^{2m}`.

`scalarMatrixPoint_splitIso`: let `z` be an affine `L`-point of `σ.normOneIsometryGroup q`
whose tensor unit (`σ.normOneIsometryAffinePointsEquiv`) is a constant `1 ⊗ M` with
`M ∈ M_m(D)`. Move `z` to the base change by `(Lie.affineBaseChangeEquiv F L _ L).symm`,
then through `splitIso` and into the scalar isometry group. The resulting scalar matrix
point is `chartN e m L (1 ⊗ M)`, the Morita split matrix of `M`.

The proof identifies composition with `splitIso` with `NormOneSplit.splitPointsEquiv` on
test schemes, and the base-change point with the pullback of `z`
(`Lie.affineBaseTestIso`). It shows that the unit point `NormOneSplit.unitPoint` of the
moved point is still the constant `1 ⊗ M`: coefficient maps fix constants, and
`FiniteAlgebraUnits.pointsEquiv_naturality` and
`Corepresented.pointsEquiv_eq_affinePointsEquiv` relate the unit points. It then applies
`scalarMatrixPoint_normOne`, `NormOneSplit.matrix_splitPointsEquiv`,
`NormOneSplit.matrixPoint_val` and `chartN_one_tmul`. The last step compares entries through
`affineSectionsIso`, entrywise as an algebra map (`AlgHom.commutes`).

## Provenance

Both results are bookkeeping between the Library's descriptions of points of norm-one
isometry groups on affine tests and on test schemes, and the Morita splitting of
quaternionic forms. They are derived from the declarations named above.
