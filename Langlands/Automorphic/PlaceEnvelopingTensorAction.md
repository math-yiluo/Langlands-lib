# Actual two-place enveloping tensor actions on original automorphic vectors

For a number field `F : Type u`, natural rank `n` and an existing actual
`OperatorRealization F n`, this module constructs two-place enveloping
tensor-product algebra actions on the original `S.Space`. The coefficient
field is complex. All natural ranks and the arbitrary number-field
universe are retained.

Actual real-place enveloping operators commute at distinct real places,
complex-place operators commute at distinct complex places, and every
real-place operator commutes with every complex-place operator. The
proof applies the original global enveloping action to the proved
commutation of the actual included algebra elements and uses its
multiplication preservation.

`realPlacesEnvelopingTensorAction`,
`complexPlacesEnvelopingTensorAction` and
`realComplexPlacesEnvelopingTensorAction` compose the constructed actual
two-place algebra tensor maps with the original genuine global
differential. These are unital complex algebra homomorphisms into the
original endomorphism algebra. Same-type place pairs retain their explicit
distinctness hypothesis. At complex places, each factor still uses the
full underlying real matrix Lie algebra before complexification.

The pure-tensor identities identify the action with the product of the
two original place enveloping operators, which acts on vectors by
composition. The original stable-function inclusion formulas compute every
tensor element's action as the existing global differential of its actual
global algebra image. These formulas cover arbitrary tensor elements,
not only pure tensors.

Every tensor action commutes with finite adelic translation by the existing
global differential commutation. Every full automorphic intertwiner
preserves the action of every tensor algebra element, by the original
full differential compatibility. Both results retain the original
coefficient space and maps.

This is an internal construction from `PlaceEnvelopingAction`,
`ArchimedeanPlaceEnvelopingTensor` and the actual global algebra action.
It introduces no original-literature assertion, topology or normalization.
No tensor decomposition of the coefficient carrier, faithful tensor
action, irreducible archimedean factor or Langlands attachment is claimed.

The local additive-group instances have explicit module-specific names,
so this module can be imported together with the actual place compact
and Lie covariance modules without generated declaration-name collisions.
Each instance uses the original submodule additive-group structure.
