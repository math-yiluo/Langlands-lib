# Ordinary matrix coordinates for scalar norm-one isometry points

The scalar chart identifies `R ⊗[K] Mₙ(K)` with `Mₙ(R)` for every commutative
`K`-algebra `R`. It carries the base-changed scalar matrix involution to
transpose, the base-changed quadratic kernel to ordinary alternating matrices
`U - Uᵀ`, the isometry defect to `g Q gᵀ - Q`, and canonical reduced norm to
determinant. The coefficient algebra may have nilpotents.
The chart also commutes with every coefficient-algebra homomorphism.

Applying these identities to the published arbitrary-test range criterion
gives exact ordinary matrix equations for the actual norm-one isometry
subgroup on every test scheme, using its algebra of relative global sections.
The ambient finite nonempty index type lies in `Type`, and the ground field
and coefficient algebras have arbitrary universe `u`.

The proofs are internal transport through Mathlib's matrix tensor algebra
equivalence, the canonical scalar splitting chart for reduced norm, and the
Library's norm-one kernel. No new literature translation or group
classification claim is introduced.

`matrixEquiv` uses the scalar tensor chart in `OrthogonalMatrix/Comparison`. Its tensor, transpose, defect, alternating-kernel and naturality identities use the corresponding chart lemmas.
