# Actual matrix points of finite-algebra unit group schemes

Let `k : Type u` be a field, let `D : Type u` be an associative unital
`k`-algebra, and let `m : Type` be finite with decidable equality.
This internal unit identifies actual points of the finite-algebra unit
group of `Matrix m m D` with invertible matrices over the appropriate
coefficient tensor algebra. The algebra `D` may be noncommutative.
No division-ring or central-simple-algebra hypothesis is used.

The algebra equivalence `MatrixPoints.coefficientEquiv k D R` moves a
commutative coefficient extension through the finite matrix algebra:

`R ⊗[k] Matrix m m D ≃ₐ[k] Matrix m m (R ⊗[k] D)`.

It composes Mathlib's `matrixEquivTensor`, the tensor associator and the
inverse matrix/tensor equivalence. The theorem
`coefficientEquiv_tmul_single` computes it on a scalar tensor a matrix
unit. Finite matrix-unit expansion then gives
`coefficientEquiv_tmul`: the `(i,j)` entry of the image of `r ⊗ M`
is `r ⊗ M i j`.
Tensor induction proves compatibility with every coefficient-algebra map
in `coefficientEquiv_naturality`.
The theorem `coefficientEquiv_lid` verifies compatibility with the actual
base-field tensor-unit equivalence.

Fix a finite basis `b : Basis (Fin d) k (Matrix m m D)`.
The equivalence `affineMatrixEquiv k D b R` composes the actual affine
point equivalence of `FiniteAlgebraUnits.groupScheme b` with
`coefficientEquiv` on units. Its target is
`Matrix.GeneralLinearGroup m (R ⊗[k] D)`, interpreted as the units of
the actual matrix ring.
The theorem `affineMatrixEquiv_naturality` identifies every actual affine
test change with entrywise coefficient extension.

The equivalence `tensorMatrixEquiv k D b T` gives the corresponding
matrix model on every relative test scheme `T`, using its actual
relative global-section algebra `((algΓ k).obj T).unop`.
The theorem `tensorMatrixEquiv_naturality` identifies actual test pullback
with the actual tensor coefficient map applied entrywise.
Both naturality statements use `Units.map` of the matrix ring
homomorphism, so they require no commutativity of the matrix coefficients.

The provenance is internal composition of the proved actual algebra-unit
point comparisons, Mathlib's matrix/tensor algebra equivalence and tensor
associativity. The entry and pullback formulas are proved here.
The construction supplies a matrix point model; elementary-root
morphisms, their norm-one lifts, and the general local Kneser–Tits theorem
remain separate obligations.
