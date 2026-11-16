# A single affine etale cover carrying a parabolic model

This internal construction starts with the explicit proposition
`RelativeParabolicEtaleLocalFiniteTypesStatement`. For a reductive group
scheme over any compact base scheme, it produces one affine scheme with
an etale surjection to the base and an actual smooth proper model of the
parabolic presheaf of the pulled-back group. In particular this applies to
an affine base. It does not prove the finite-types proposition or effective
scheme descent from this cover.

`SmoothProperModel.forComposite` transports a supplied model for a direct
base change to the iterated base change along two maps whose composite is
the original map. It uses the canonical parabolic-presheaf base-change
isomorphisms, the slice functors' composition and equality isomorphisms,
and the functor associator. The representing scheme and its structure map
remain the same, so its smoothness and properness certificates apply.

`SmoothProperModel.coproduct` works with any family indexed in the base
universe. The canonical open cover of the coproduct by its components,
the preceding composite-map transport and `SmoothProperModel.zariskiGlue`
assemble supplied models over all components into one model over that
coproduct base. No finiteness or affineness hypothesis is used in this step.

`AffineEtaleCoverModel` records an actual affine covering scheme, its
etale surjective structure map and a `SmoothProperModel` of the actual
pulled-back group. The latter represents actual parabolic subgroup
families on the full slice category; its universal relative-parabolic
family is available through `SmoothProperModel.universalFamily`.

For `nonempty_affineEtaleCoverModel`, the finite-types proposition supplies
an affine etale neighbourhood and smooth proper model at each point by
`affineEtaleModel`. Each neighbourhood map has open image because etale
maps are flat and locally of finite presentation and hence universally
open. Compactness supplies a finite selection of these images covering
the base. The coproduct of the selected affine schemes is affine because
the family is finite. Its structure map is etale by Zariski locality at
the source, and it is surjective because the selected images cover. The
preceding coproduct construction supplies the actual smooth proper model
over that same covering scheme. The argument includes the empty base.

`affineEtaleCoverModel` chooses this proved cover and its model. All
constructions retain the stated base universe and the explicit finite-types
hypothesis. They are internal compositions of imported actual-model,
base-change, compactness and scheme-coproduct results, with no new
literature translation claimed. The unconditional global parabolic
representability theorem remains a separate obligation.
