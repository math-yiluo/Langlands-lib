# Algebraic adapters for the regular tempered standard module

Author: Worker 156.

This module constructs `Langlands.RegularHeadExistence.standardModuleLeviTwistEquiv`:
an actual intertwining linear equivalence from the standard module of a tempered
Langlands datum to normalized upper induction of the Levi real-power twist of
its untwisted block tensor. Its two accompanying lemmas identify the tensor
actions and transport an assumed irreducible head to the actual smooth canonical
head quotient. These are internal algebraic consequences of published Library
constructions, not additional analytic results attributed to the literature.

## Tensor identity

`blockTensor_twistedBlocks` applies to any smooth family on the blocks of an
actual `GeneralLinear.BlockShape`, with arbitrary real exponents. It bundles the
real Levi character with its published open-kernel certificate. Evaluating this
character at a single coordinate reduces its finite product to that coordinate's
determinant-power character. The published
`Induction.SmoothCharacter.external_coordinate_twist` then identifies the tensor
of the individually twisted smooth blocks with the real twist of the untwisted
tensor. This is equality of the actions on the same tensor carrier.

## Induced equivalence and conditional head transport

`standardModuleLeviTwistEquiv` applies the published
`T.normalizedParabolicInducedEquiv` to that tensor equality. Its source is exactly
`d.standardModule.representation`; its target is normalized upper induction of
`T.leviRealPowerTwist d.shape d.exponent` applied to the untwisted block tensor.
Both sides use the actual function-space induction construction and its modulus.

`standardModule_hasHead_of_leviTwistHead` assumes that the latter representation
has an irreducible head. Source-equivalence transport
`Classification.IsIrreducibleHead.of_equiv` preserves the strong head condition,
including equality of the kernel with every surjective map to an irreducible
representation. The published equivalence
`SmoothRep.isIrreducibleHead_headQuotient_iff` then supplies
`d.IsLanglandsHead d.standardModule.headQuotient`. The head quotient is an actual
smooth representation, not an isomorphism-class placeholder.

The field and block-carrier universes `uF` and `uV` remain independent. The induced
carrier and the smooth head quotient use `max uF uV`. No strict-order condition,
positivity, or analytic consequence of temperedness is used by these adapters.
They do not prove their head premise or the closed
`Langlands.GLRegularLanglandsHeadExistenceStatement`; analytic support and
comparison results are still needed for that theorem.
