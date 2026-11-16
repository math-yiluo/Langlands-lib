# Actual Lie determinants of parabolic representatives

For any actual parabolic subgroup functor `F` of a group scheme over an arbitrary
scheme `S : Scheme.{u}`, this module compares its actual relative parabolic
representatives. `ParabolicRepresentative.iso r r'` is the existing unique group
isomorphism compatible with their inclusions into the ambient group. Its
characterization, identity and cocycle laws follow by cancellation of the
representing inclusion.

`r.lieDeterminant` is the actual determinant line of `r.group.Lie`, using the
smoothness proved by its relative parabolic predicate. The comparisons
`r.lieDeterminantChangeIso r'` apply the Lie functor and actual determinant to
the inclusion-compatible group isomorphisms. Their identity and cocycle laws
follow from those group laws and composition of determinant isomorphisms.
There is no constant rank assumption and no reductivity premise for these
same-base constructions.

For a reductive ambient group over a base `B`, and a representative over an
object `M : Over B`, `r.restrict hH a` constructs an actual representative of
the restricted parabolic subgroup along `a : T ⟶ M`. Its group is the actual
base change of `r.group`, and its inclusion is the existing `familyHom` into
the specified base change of the ambient group. The established independence
of subgroup evaluation from a representative proves that this represents
exactly the restricted subgroup. `iso_restrict` proves that the canonical
comparison of restricted representatives is the base change of the original
group comparison, by its compatibility with the evaluated inclusions.

`restrictLieDeterminantIso` is the actual smooth Lie determinant base-change
isomorphism for this representative. Its naturality theorem states that
restriction commutes with the canonical determinant changes of representatives.
The proof uses `iso_restrict` and the general smooth Lie determinant naturality
square.

This is internal derived API from the represented-subgroup uniqueness theorem,
the actual parabolic restriction construction, and the actual smooth Lie
determinant. It supplies no identity or composition coherence in the base
morphism, no dual determinant, no ampleness, and no proof of global parabolic
representability.
