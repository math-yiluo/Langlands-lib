# Explicit contraction of the actual upper root of split SL₂

For an arbitrary commutative ring `R : CommRingCat.{u}`,
`SpecialLinear.BinaryRoot.upperCocharacter R` is the actual group-scheme
homomorphism from `Gm (Spec R)` to `SpecialLinear.groupScheme (Fin 2) R`
whose matrix on every relative test scheme is `diag(t,t⁻¹)`.
The theorem `upperRoot_range_le_dynamicUnipotent` proves that the actual upper
additive root image lies in the dynamic unipotent subgroup of this cocharacter,
as an inclusion of subgroup functors on all schemes over `Spec R`.
There is no restriction on characteristic or on the test scheme.

This is an internal construction from the existing matrix descriptions of the
special linear and multiplicative group schemes and the actual root map in
`SpecialLinearBinaryRootGroups`. The matrix `contractingMatrix t` is the
existing `BinaryUpper.diagonalMatrix` applied to `t⁻¹`. Its multiplicativity
and compatibility with change of coefficient ring yield a natural
homomorphism on all test-scheme point groups. The existing group-valued
Yoneda construction `homOfPoints` gives `upperCocharacter`. The theorem
`pointsEquiv_upperCocharacter` verifies its matrix formula.

Direct binary matrix multiplication proves
`contractingMatrix_conjugate_upper`: conjugation by `diag(t,t⁻¹)` sends the
upper transvection with coefficient `x` to the upper transvection with
coefficient `t²x`. For an actual additive-root point on `T`,
`upperContraction` is the point on `T × A¹` corresponding to the upper
transvection with coefficient `s²x`, where `s` is pulled back from the standard
affine-line coordinate and `x` is pulled back from the existing additive
coordinates on `T`.

The theorem `pointsEquiv_comp_upperContraction` calculates this curve after
every change of test scheme. Restricting it along `Gm → A¹` replaces `s` by
the underlying global unit. The conjugation identity then proves
`upperContraction_isOrbitExtension`, with the exact orbit used by
`Dynamic.IsOrbitExtension`. Restricting along the zero section sets the
coefficient to zero, so `upperContraction_evalZero` gives the identity point.
These two properties are precisely the witness required for membership in
`Dynamic.unipotent`. Applying the construction to each point in the actual
root-map range proves the subgroup-functor inclusion.

This unit proves the explicit split binary contraction. It does not construct
split SL₂ presentations of arbitrary factors, prove the structural conjugacy
or relative-root generation inputs for an ambient group, or prove the
unrestricted local Kneser–Tits statement.
