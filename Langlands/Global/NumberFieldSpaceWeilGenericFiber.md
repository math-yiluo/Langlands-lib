# Original generic-fibre comparison of a number-field space Weil model

This internal unit identifies the original integral Weil model's generic fibre,
proves its compatibility with the canonical full adelic tensor map, and constructs
the field-valued adelic homeomorphism for these specified models. Algebraicity
and separated finite-type geometry of the integral Weil model remain explicit
inputs; arbitrary independent models are not compared in this unit.

Let `L/K` be an extension of number fields and `S` a finite set of finite places
of `K`. Let `X` be an algebraic space over the original upper S-integers, where
the upper support is the full preimage of `S`, and assume its original Weil
sheaf to the lower S-integers is algebraic.

`genericWeilAlgebraic` applies the published cartesian Weil base-change result
to the original fraction-field tensor equivalence. Its right pure-tensor law
is the original inclusion of the upper integral coefficients into `L`.
`genericFiberIso` is that actual cartesian isomorphism from the generic fibre
of the original integral Weil space to the field Weil space of `X`'s generic
fibre. No identification of abstract isomorphism classes replaces these maps.

`adeleInclusion_compatible` records the original full adele inclusion on field
coefficients. `adelicEvaluation_model` identifies the canonical field Weil
point equivalence, after the lower generic-fibre spread equivalence, with the
integral counit evaluation followed by the upper generic-fibre equivalence.
The proof retains the original lower and upper S-integer actions through explicit
scalar towers. It applies injectivity of the upper base-change point equivalence,
replaces the canonical tensor point map by original counit evaluation using its
unit-tensor formula, and uses the general cartesian counit evaluation comparison.
The inverse identities of the generic-fibre point equivalences finish the proof.

For a specified isomorphism `e` from `X`'s generic fibre to a space `Y` over `L`,
and an explicit algebraicity proof for the Weil sheaf of `Y`, `genericFiberIsoOfIso`
composes `genericFiberIso` with the actual Weil restriction of `e`.
`adelicEvaluation_modelOfIso` proves the corresponding adelic square. This follows
from the naturality of the canonical tensor point equivalence in the original
space and the preceding generic-fibre square.

Assume further that `X` and its original integral Weil space are separated and
of finite type. `adelicPointHomeomorphOfIso` composes the inverse lower spread
homeomorphism, the full integral-model Weil homeomorphism, and the upper spread
homeomorphism. Its source topology is the spread topology attached to the actual
integral Weil model and `genericFiberIsoOfIso`; its target topology is the spread
topology attached to `X` and `e`. `adelicPointHomeomorphOfIso_apply` proves that
its forward map is precisely `numberFieldSpaceWeilRestrictionPointsEquiv`, hence
the canonical map specified in the adelic Weil theorem. The proof represents
an arbitrary source point by the lower spread equivalence, cancels that
equivalence with its inverse, and applies `adelicEvaluation_modelOfIso`.

The provenance is internal composition of the actual integral-closure fraction
tensor equivalence, cartesian Weil base change, counit evaluation compatibility,
canonical full adelic tensor comparison, and the proved fixed-model and spread
homeomorphisms. All original infinite-place factors and coefficient maps are
retained through these published constructions.
