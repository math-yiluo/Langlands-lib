# Coefficients of actual additive tensor representations

This internal derived construction uses supplied actual representations `ρ` and
`σ` of the additive-group scheme over a field `k : Type u`, on finite coordinate
types `n` and `m`. The representation `ρ.tensor σ` is the published actual
tensor representation of the same group scheme. It acts on the full tensor
product in the product-basis coordinates of `CoordinateTensor`.

`tensorCoefficientOperator ρ σ a b` is the linear endomorphism whose matrix is
`D_a(ρ) ⊗ₖ D_b(σ)`. Here `D_a` denotes the coefficient matrix of the universal
univariate representation matrix. Its coordinate comparison proves that it is
exactly the tensor product of the two actual coefficient endomorphisms.

The universal matrix of `ρ.tensor σ` is the Kronecker product of the two
universal matrices. Consequently its degree `d` coefficient matrix is

`Σ_(a+b=d) D_a(ρ) ⊗ₖ D_b(σ)`.

The same convolution holds for the linear coefficient endomorphisms. The proof
uses the published actual affine tensor matrix formula, the univariate matrix
definition and the polynomial coefficient-of-product identity.

In prime characteristic `p`, for every `e` and `d < p^e`, the degree `d`
coefficient of `ρ.tensor (σ.frobeniusPower p e)` is
`D_d(ρ) ⊗ₖ 1`. The powered factor has zero positive coefficients below `p^e`;
the convolution therefore retains only its constant coefficient, which is the
identity. The final theorem identifies this operator on the full module tensor
product with `D_d(ρ)` tensored with the identity.

No infinite-field or perfectness premise is used. Frobenius is the actual
postcomposition already constructed in `MatrixRepresentation.FrobeniusPower`.
These results do not assume a bound on the first factor's polynomial degree,
and assert neither tensor irreducibility nor existence of root subgroups or
Steinberg modules. They do not prove `SteinbergBigCellStatement`.
