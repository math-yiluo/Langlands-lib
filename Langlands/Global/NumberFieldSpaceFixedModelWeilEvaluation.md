# Original counit evaluation on number-field space stages

This internal unit identifies the previously constructed fixed-model Weil stage
homeomorphism with evaluation of the original algebraic-space counit. It also
proves the resulting square with the literal full adele inclusions. It does not
assert the full adelic homeomorphism or independence of models.

Let `L/K` be an extension of number fields, let `S` be a finite support of `K`,
and let `T` contain `S`. The integral bases are the original lower S-integers
and upper integers outside the full preimage of `S`.

`levelInclusion` restricts the original `adeleInclusion` to the lower `T`-level
and the upper level outside the full preimage of `T`. Its construction uses the
published equivalence between integrality of a completion image and integrality
of its source. `levelInclusion_compatible` proves compatibility with the two
integral bases using the original diagonal inclusion formula.
`levelInclusion_coordinate` identifies every upper local projection of this
level inclusion with the original local coefficient map. It uses the published
full-adele projection formula, including the original integer subtype at
integral coordinates.

`upperLevelFactorAlgHom` expresses that upper projection as an algebra
homomorphism into its regrouped original local factor. Its scalar condition
holds by the original coefficient definitions in the infinite, finite-field,
and finite-integer cases. This records the same ring map with the coefficient
algebra expected by the original local tensor comparison.

Let `X` be an actual algebraic space over the upper integral base. Assume that
`X` is separated and of finite type, that its actual Weil sheaf is algebraic,
and that its Weil space is separated and of finite type.
`adelicLevelPointHomeomorph_eq_evaluation` proves that the actual stage
homeomorphism equals `spaceWeilRestrictionEvaluation` along `levelInclusion`.
The proof applies injectivity of the upper stage coordinate homeomorphism,
uses surjectivity of the original place reindexing, and replaces each local
tensor counit component by its evaluation formula. Case analysis makes the
factor regrouping the identity, and upper coefficient naturality together with
`levelInclusion_coordinate` proves the desired coordinate equality. All
infinite factors and the original completed integer coefficient actions remain
present.

`adelicEvaluation` is the original integral Weil counit evaluated along the
literal full adele inclusion. `adelicEvaluation_stage` proves that evaluation
after the lower stage inclusion is the stage homeomorphism followed by the
upper stage inclusion. After replacing the stage homeomorphism by the preceding
identity, the proof applies lower and upper coefficient naturality; both
coefficient composition equations are the literal inclusion identities.

The provenance is internal: these identities follow from the published original
local coefficient and projection formulas, the actual fixed-level space Weil
homeomorphism and its coordinate formula, and the general space counit
evaluation naturality API. Representability, finite-type geometry, and
separatedness of the Weil space are retained as explicit inputs here.
