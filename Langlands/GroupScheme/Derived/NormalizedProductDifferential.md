# Normalized multiplication from tangent spanning

Author: Worker 1447.

This internal construction applies to three actual smooth affine group schemes
`D`, `T`, and `G` over any field, in an arbitrary common universe. The ambient
scheme `G` is connected. The two homomorphisms are `d : D → G` and `i : T → G`.
Its explicit linear hypothesis is that the sum of the images of their actual
identity differentials, computed by dual numbers over the ground field, is all
of `Lie(G)`.

`AutomorphicAction.smoothSurjective_of_tangentSpan` also takes an actual action
of `T` on `D` compatible with conjugation through the two homomorphisms. It
forms the published semidirect multiplication homomorphism. The two factor
inclusions into this semidirect group show that both tangent images lie in its
differential image. The spanning hypothesis therefore makes that differential
surjective. The published actual-differential criterion then gives smoothness
and scheme surjectivity. The underlying semidirect multiplication map is
exactly `subgroupProductMap d i`, with `D` first.

`smoothSurjective_subgroupProductMap_of_normal_of_tangentSpan` takes normality
of the first subgroup range on all test schemes and monicity of its underlying
relative morphism. Normality provides the compatible conjugation action, so
the preceding construction applies. It makes no commutativity assumption on
`T`, nor any reductivity assumption on `G`.

The provenance is internal composition of the published semidirect-product
maps and `Lie.smoothSurjectiveOfSurjectiveDifferential`. In the derived-subgroup
application, proving the tangent spanning hypothesis remains a separate
mathematical obligation. This module does not prove the unrestricted
`DerivedMaximalTorusProductSurjectivityStatement`.
