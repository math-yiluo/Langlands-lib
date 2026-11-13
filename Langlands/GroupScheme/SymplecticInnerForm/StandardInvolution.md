# The standard symplectic involution and the adjoint algebra action

Over any commutative ring `R` and finite index type `n`, `standardInvolution`
is the first-kind involution `x ↦ -J xᵀ J` on matrices indexed by `n ⊕ n`,
where `J = Matrix.J n R`. The identity `J² = -1` proves the anti-multiplicative
and order-two laws in every characteristic. The empty index type is allowed.

`standardInvolution_mul_J` records `τ(x) J = J xᵀ`.
`standardInvolution_symplectic` identifies `τ(g)` with the inverse of a
symplectic matrix. `standardInvolution_map` proves compatibility with arbitrary
homomorphisms of commutative coefficient rings.

Given a supplied adjoint quotient and a supplied split symplectic presentation,
`adjointMatrixHom_standardInvolution` proves that the previously constructed
algebra action commutes with this involution. Both composites are linear maps.
On symplectic matrices the involution is inversion, and the action agrees with
the actual inner group action, which preserves inversion. The full symplectic
linear span then gives equality on the entire algebra.

These are derived internal matrix identities using the published symplectic
matrix inverse and span interfaces. They do not assert existence of a descended
algebra or prove the host inner-form classification.
