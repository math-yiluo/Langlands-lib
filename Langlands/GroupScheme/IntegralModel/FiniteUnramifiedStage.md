# Finite unramified stages of specified smooth integral models

This internal construction is a step toward integral-model descent. All fields
and schemes remain in an arbitrary universe `u`. Let `F` be a nonarchimedean
local field, `G` a group scheme over `F`, and `N` an integral model of its scalar
extension to the inertia fixed field. Supply `D : SpectralGroupModel F N.group`,
which has a smooth affine integral group over the actual spectral integers of a
finite Galois arithmetically unramified intermediate field of the chosen
separable closure.

`stageIntegerInclusion` is the actual ring map induced by an inclusion of two
intermediate fields. Its well-definedness follows by comparing both spectral
norms with the norm in the common separable closure. `stageIntegerMap` is its
spectrum. `stageIntegerMap_generic` and `stageIntegerMap_inertia` give the exact
commuting squares with the generic inclusions and the maximal-unramified
integer inclusions. `spectralIntegerMap_generic` gives the corresponding square
at one stage; `fieldSpecMap_base` identifies the field inclusion followed by the
base-field map.

`stageIntegralComparison` compares the iterated integer extension with the
direct one. `inertiaGenericSquare` and `enlargementGenericSquare` compare generic
fibres after integral extension with field extensions of the generic fibre.
Each is built from the actual `pullbackComparison` isomorphisms. Their `_fst`
lemmas state preservation of the projection to the original group. The private
`squareComparison_fst` proof reduces this to the forward and inverse projection
laws for direct versus iterated pullbacks.

`stageGenericComparison` uses `N.genericIso`, the supplied `D.iso`, and these
canonical comparisons to give a specified isomorphism over the inertia fixed
field between the extensions of `G` over `D.field` and the generic fibre of
`D.group`. Affineness of `G` follows from the existence of `N`: the generic
fibre of the affine integral model is affine, its specified generic isomorphism
transports this property, and fpqc descent along the field extension reflects
affineness. No affineness assumption on `G` is added.

`nonempty_modelIsoStage` applies `nonempty_isoStage` to this specified
isomorphism, using the affine source and smooth target to supply its finiteness
hypotheses. `modelIsoStage` chooses the resulting finite Galois arithmetically
unramified enlargement. The `IsoStage` includes an exact recovery equation for
the specified generic isomorphism.

For any such enlargement `A`, `enlargedGenericIso` combines the generic square,
`A.iso.symm`, and the base-field comparison. `enlargedModel` has integral group
obtained by base change of `D.group` along `stageIntegerMap F A.contains`, with
this chosen generic identification. Affineness, flatness, finite type, and the
separate theorem `enlargedModel_smooth` follow by base change of the properties
of `D.group`. `enlargedModelIso` compares the scalar extension of its integral
group to `N.group`, via `stageIntegralComparison` and `D.iso.symm`.

This unit constructs the finite integral model and the comparison of its
integral group. It does not yet assert that `enlargedModelIso` is compatible with
the two specified generic identifications in the sense of `IntegralModel.Iso`;
that requires a further coherence proof from the `IsoStage.recovery` equation.
It also does not construct semilinear descent data or assert effective descent.

The provenance is internal. The mathematical inputs are the spectral group
model, finite unramified isomorphism-stage construction, and fpqc affineness
descent imported by Lean name. The maps and comparison proofs here are derived
from those constructions and the actual pullback universal properties.
