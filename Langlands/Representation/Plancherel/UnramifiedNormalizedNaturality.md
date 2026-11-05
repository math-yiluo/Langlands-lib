# Naturality of normalized specialization

Worker 1585. This is a derived construction from the actual tensor,
full smooth induction, relation quotient, and specialization modules.
Waldspurger 2003 I.5, printed p.245, and IV.1, printed p.277
(`waldspurger-2003-plancherel`), supply the motivating B-coefficient and
evaluation conventions. No algebraic-family finiteness or fiber
isomorphism is asserted.

`complexInducedMap` applies the existing `Induction.smoothInducedMap`
to a complex coefficient intertwiner, twisted by χ, inflated along the
actual Levi projection, and twisted by the positive full-P half-character.
Its value formula is pointwise postcomposition by the original coefficient
map. Its identity and composition proofs use extensionality of functions.
`complexInducedMap_heq_functor` identifies it by heterogeneous reflexivity
with the map
of the existing normalized induction functor after the smooth twist functor.
That categorical comparison uses one common carrier universe; the raw maps
and all naturality identities retain independent coefficient universes.

`complexJacquetMap` descends that induced map using the actual
`Jacquet.Localization.map` at character one and then the common inverse
Levi half-character. Its class formula is exactly [f] ↦ [T(f)], with the
pointwise induced map inside the class. Identity and composition are
proved after the surjective canonical quotient map, using the corresponding
induced-map laws. These are the existing complex quotient and twist map
constructions on the targets identified with the normalized functors in
`UnramifiedNormalizedSpecialization`.

`tensorEvaluation_natural` is the published tensor evaluation identity
for the scalar-extended coefficient map. `inducedEvaluation_natural`
proves the corresponding square on full smooth functions by evaluating
each value and using that tensor identity.
The generic helper `quotientEvaluation_natural` reduces a commuting square
of equivariant semilinear coefficient maps to representatives in the actual
character-one relation quotients. `jacquetEvaluation_natural` applies it
to the full induced evaluation square. Thus evaluation commutes with the
actual B-linear induced and normalized Jacquet maps of every complex
coefficient intertwiner, along the same scalar evaluation B → ℂ.
The entire supplied norm family and the original normalization signs are
retained; no full-P/inflated-Levi character comparison is used.
