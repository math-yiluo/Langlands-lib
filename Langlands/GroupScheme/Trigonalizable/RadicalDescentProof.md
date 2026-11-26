# Separable trigonalizability and descent of the geometric unipotent radical

`Langlands.GroupScheme.separablyTrigonalizableRadicalDescent` proves
`SeparablyTrigonalizableRadicalDescentStatement.{u}` for every universe `u`.
It applies over any field to a smooth connected affine solvable group `G`.
It characterizes becoming trigonalizable over a separable algebraic
extension of the ground field by descent of the geometric unipotent radical
as a closed subgroup of `G`. [Statement](RadicalDescentStatement.md)

## Proof

Suppose `G` becomes trigonalizable over a separable algebraic extension.
The separable criterion gives a closed normal unipotent subgroup `U` and
an fppf quotient with target of multiplicative type. Over the algebraic
closure, the base-changed quotient still has a target of multiplicative type
and its kernel is the base change of `U`. The group over the algebraic
closure is also smooth, affine, connected and solvable. The theorem
`solvableTorusQuotient` gives it a split-torus quotient with smooth connected
normal unipotent kernel `V`. Each kernel is greatest among closed unipotent
subgroups because every homomorphism from a unipotent group to a group of
multiplicative type is trivial. [Separable criterion](SeparableCriterionProof.md),
[Split-torus quotient](../Absolute/SolvableTorusQuotientProof.md),
[Greatest unipotent subgroups](GreatestUnipotent.md)

The two greatest kernels therefore have the same range on every test scheme.
The smooth connected kernel `V` represents the unipotent radical.
`IsUnipotentRadical.of_range_eq` transfers this property to the base change
of `U`, and `IsUnipotentRadical.of_baseChange` reflects the radical properties
back to `U`. The two radical predicates give the required
`IsGeometricUnipotentRadical` witness for the inclusion of `U` in `G`.
[Transfer along equal ranges](../Reductive/SmoothQuotientRadicalExtension.md),
[Reflection along a field extension](../Rational/UnipotentRadicalProperties.md),
[Comparison of geometric radical predicates](../Rational/GeometricUnipotentRadicalComparison.md)

Conversely, let `i : U ⟶ G` represent the descended geometric radical.
`LeviSubgroup.IsGeometricUnipotentRadical.torusQuotient` constructs the
smooth fppf quotient of `G` by the range of `i`. It identifies the quotient
after base change to the algebraic closure with a split-torus quotient of
`G` over that field. The quotient over the ground field is thus a torus and
is of multiplicative type. Applying the separable criterion to `i` and this
quotient gives a separable algebraic extension over which `G` is trigonalizable.
[Quotients by geometric radicals](../Rational/GeometricRadicalTorusQuotient.md)

## Source

James S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite
Type over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Corollary 16.31 and its proof are on printed p. 335 (PDF p. 351).
The proof uses Theorem 16.6 on pp. 325–326 (PDF pp. 341–342) and the
algebraically closed case of Theorem 16.33(a)–(c) on pp. 335–336
(PDF pp. 351–352).
