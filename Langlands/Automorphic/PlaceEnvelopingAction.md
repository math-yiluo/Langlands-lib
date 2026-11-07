# Genuine place enveloping actions on the original automorphic carrier

For a number field `F : Type u`, natural rank `n` and an existing
`OperatorRealization F n`, this module constructs unital complex algebra
actions of the actual real-place and complex-place enveloping algebras
on the unchanged `S.Space`. All natural ranks, including zero, and the
arbitrary number-field universe are allowed.

`realPlaceEnvelopingAction` and `complexPlaceEnvelopingAction` compose the
original genuine global enveloping action with the injective actual
place enveloping inclusions. The second local algebra retains the full
underlying real complex matrix Lie algebra before complexification.
The two action objects are unital complex algebra homomorphisms into
the original endomorphism algebra.

The generator identities identify every local Lie generator's action
with the already constructed original place Lie action. Universal
enveloping extensionality then proves that the action on the entire
local algebra is exactly the universal extension of that original Lie
action. Thus neither a new differential nor a replacement representation
carrier is supplied.

The inclusion identities compute each local enveloping operator on the
original embedded stable automorphic functions: it is precisely the
original global differential evaluated on the actual included algebra
element. Every local enveloping operator commutes with finite adelic
translation, by the original finite/global differential commutation.

Full automorphic intertwiners preserve the action of every element of
each actual local enveloping algebra. Their restrictions are genuine
intertwining maps of the underlying multiplicative monoid representations,
with the original complex linear maps unchanged. Full equivalences
similarly retain the same complex linear equivalences on those local
actions.

This is an internal construction from `PlaceLieAction`,
`ArchimedeanPlaceEnveloping`, the original global differential and full
intertwiner operations, and pinned Mathlib's universal enveloping
extensionality. It introduces no original-literature assertion, topology
or normalization. It does not assert that the action is faithful, extract
irreducible archimedean factors, or construct a Langlands attachment.
