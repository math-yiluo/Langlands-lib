# Hyperbolic norm-square torus

Authors: Worker 124.

This internal construction identifies the diagonal-torus restriction of the
actual binary quaternion product action with the canonical norm-square
unit pairs. Its prerequisites are the actual involution and reduced norm,
`BinaryQuaternionAction`, `NormSquareCover`, and the Library's binary
special-linear diagonal matrices. No classification or comparison with a
supplied spin cover is assumed.

Over a commutative ring `R` and an `R`-algebra `A`, `hyperbolicLevi σ` is
the actual homomorphism

```
a ↦ diag(a, σ(a⁻¹)).
```

`diagonalSL` uses the existing `SpecialLinear.BinaryUpper.diagonalMatrixHom`
with the inverse unit as input, so its diagonal is `(t,t⁻¹)`.
`diagonal_action_eq_levi` computes the product action on this torus: if
`σ(b⁻¹) = ℓ⁻¹bℓ`, its value at `(diag(t,t⁻¹),b)` is the hyperbolic Levi
matrix of `scalar(t)b`. This is an equality of actual matrix units.

For the original central division algebra of dimension four,
`normSquareSpinTorus` maps a norm-square pair `(a,t)` into
`SL₂(R) × SL₁(D)(R)`. Its coordinates are the scalar diagonal matrix of
`t` and the norm-one part `a·scalar(t)⁻¹`. The previously constructed
`normSquareProductEquiv` supplies the latter as an actual group
homomorphism. The coordinate lemmas and `normSquareSpinTorus_product`
record both directions of this product description. The construction
itself depends on the dimension-four hypothesis, not on an involution.

`exists_diagonalSL_of_offDiagonal_eq_zero` compares the action's two
off-diagonal entries. Invertibility of `b` and `ℓ`, together with
injectivity of the scalar map, forces the two off-diagonal entries of
the scalar matrix to vanish. Its determinant then supplies a unit `t`
with the prescribed diagonal matrix. Applying this to the actual tensor
algebra proves `exists_normSquareSpinTorus_of_eq_levi`: every product
point whose image equals the hyperbolic Levi matrix of `a` comes from
a norm-square pair with first coordinate `a`. Consequently
`norm_square_of_normOneAction_eq_levi` produces an actual unit square
root of the reduced norm. These implications do not require an
infinite-field hypothesis.

Over an infinite ground field, `normOne_conjugate_inv` derives the
inverse-conjugation relation from the all-coefficient reduced-norm
sandwich identity, applied to the inverse norm-one point. The theorem
`normSquareSpinTorus_action` then proves the converse action formula:
every norm-square pair maps to the hyperbolic Levi matrix of its first
coordinate. These results hold for every commutative coefficient algebra,
including nonreduced ones, without a characteristic restriction.

The unit identifies a preimage inside the concrete coefficient-group
product model. It does not identify that model with the preimage in an
arbitrary supplied spin cover, prove a central-isogeny comparison or
assert elementary generation in that cover.
