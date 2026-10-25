# Smoothness target for the actual general linear group scheme

Author: Worker 57.

`Langlands.GroupScheme.GeneralLinear.SmoothStatement` asserts that for every
small finite matrix index type `n` with decidable equality and every commutative
ring object `R : CommRingCat.{u}`, the structure morphism of the existing
`GeneralLinear.groupScheme n R` to `Spec R` is smooth. This is a proposition
definition, not a proof or a supplied smoothness field.

The target uses Mathlib's `AlgebraicGeometry.Smooth`: on affine charts, the
induced ring maps are smooth. It does not merely assert smoothness of field-valued
points. There are no field, nonzero rank, reduced-base or characteristic
hypotheses. The empty matrix index and zero ring are included. It does not assert
reductivity or the existence of any Harris Shimura scheme.

This is an internal geometric target for the group's already constructed
coordinate quotient. Its proposed proof uses the explicit algebra equivalence
with the polynomial matrix ring localized at its determinant, followed by
Mathlib's smoothness of finite polynomial algebras, localization, composition
and algebra-isomorphism transport. The affine spectrum criterion then gives
smoothness of the actual structure morphism. That comparison is a prerequisite
for the proof, not a hypothesis in this statement. The target imports only the
published general linear group and Mathlib's smoothness definitions, so its
meaning is independent of the proposed proof implementation.
