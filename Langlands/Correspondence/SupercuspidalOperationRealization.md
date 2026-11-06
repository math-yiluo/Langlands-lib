# Realization of the endpoint twist and smooth-dual relations

Author: Worker 357.

This internal derived interface specializes published operations to the actual
supercuspidal class space used by the correspondence specification. For every
prime `p`, every `F : PadicField p`, every positive rank and independent field
and representation-carrier universes, it constructs canonical twist and smooth
dual equivalences. It identifies the existing representative-based relations
with their graphs and proves existence and uniqueness of each output.

This unit does not construct a local Langlands correspondence. The final two
equivalences reformulate the existing compatibility predicates as equations.
Those equations remain conditions on a proposed family; they are not proved
for an arbitrary family.

## Canonical twists

`isOpen_ker_determinantQuasiCharacter` applies the published
`isOpen_ker_of_continuous_complex_character` to `χ ∘ det`. The canonical
general linear group is nonarchimedean by
`PadicField.canonicalGeneralLinearNonarchimedean`, and the composition is
continuous by `TopologicalData.generalLinearDeterminant` and the continuity
already included in `QuasiCharacter`. No unitarity condition is used.

`supercuspidalTwist` is the published
`GeneralLinear.SupercuspidalClass.twist` with this open-kernel proof and the
published determinant-kernel inclusion. The existing relation criterion
`isSupercuspidalCharacterTwist_iff_eq_twist` immediately identifies its graph.
The identity and multiplication laws specialize `twist_one` and `twist_twist`.
They make twisting by the inverse character an inverse map, defining
`supercuspidalTwistEquiv`. The graph criterion gives
`existsUnique_supercuspidalCharacterTwist`.

## Canonical smooth duals

`supercuspidalDual` is the published
`PadicField.SupercuspidalClass.contragredient`, supplied with the published
proof `GeneralLinear.supercuspidalContragredient`. Thus this interface has no
remaining supercuspidal-closure premise. Its involutivity is the existing
class involutivity theorem; using the same map in both directions defines
`supercuspidalDualEquiv`.

`isSmoothDual_iff_eq_contragredient` treats the full automorphic class space.
In the forward direction the witnesses in `IsSmoothDual` give equality with
the quotient contragredient by
`SmoothDualClass.contragredient_mk_eq_mk_iff`. In the reverse direction a
representative and its actual bundled contragredient supply the required
representations and equivalence. Compact-open cofinality is the published
`GeneralLinear.compactOpen_cofinal` at the canonical field topology.

`supercuspidalToAutomorphic_dual` specializes the published commuting
forgetful-map identity. Injectivity of this map then identifies the restricted
relation with the graph of `supercuspidalDual`. The graph identity gives
`existsUnique_supercuspidalSmoothDual`, and involutivity proves symmetry of the
relation.

## Compatibility and provenance

`supercuspidalTwistCompatibility_iff` and
`supercuspidalDualCompatibility_iff` apply the graph criteria pointwise.
They retain the exact continuous irreducible Weil twist and dual used in
`OperationCompatibility`, along a supplied reciprocity candidate for twists.
The field, parameter-carrier and representation-carrier universes remain
independent.

All new content is an internal composition of published declarations in
`Correspondence.SupercuspidalRelations`, `Correspondence.OperationCompatibility`,
`Representation.Classification.SupercuspidalTwist`,
`Representation.Classification.SupercuspidalContragredient`,
`Representation.Classification.SupercuspidalContragredientProof`,
`Representation.Category.Contragredient` and
`Representation.Twist.ContinuousCharacterProof`. Their paired Markdown records
the original representation-theoretic conventions and proofs. No new assertion
from external literature is claimed here, and no replacement construction of
the underlying quotient operations is introduced.
