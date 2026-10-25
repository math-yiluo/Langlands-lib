# Orbit cocones and finite-fibre preservation

This is internal categorical infrastructure for the finite-group quotient proof.
It uses the Library's actual finite étale cover category and point and fibre
functors. It does not construct a quotient scheme.

`groupOrbitCoconeIsColimit` constructs the colimit universal property for a
cocone of a group-action diagram in types. It assumes its sole cocone map is
surjective, and any two elements with equal images differ by a group element.
For a competing cocone, choose a preimage of each point and apply its cocone map.
The orbit hypothesis and cocone naturality prove the factorization equation;
surjectivity proves uniqueness. Finiteness of the group is not needed. The
indexing group's universe and the universe of the types are independent.

`fiberFunctor_preservesColimitsOfShape_large` generalizes the transfer argument
in Worker 239's published `GeometricFiniteLimitsCoproductsProof` to independent
indexing universes. It transfers preservation from the
actual type-valued point functor to the finite-set-valued fibre functor. Their
composite with the fully faithful inclusion of finite sets into types is the
same functor, and the inclusion reflects colimits. The indexing category has
independent object and morphism universes; this covers `SingleObj G` for
`G : Type u` without lowering the target's universe.

The definitions and proof arguments are derived internal categorical content,
using Mathlib's cocones, colimit reflection, and classical choice. They assert
no independent geometric existence or preservation result.
