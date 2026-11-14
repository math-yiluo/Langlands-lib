# Exact finite unramified recovery of smooth integral models

This internal construction proves
`Langlands.GroupScheme.IntegralModel.finiteUnramifiedRecovery :
FiniteUnramifiedRecoveryStatement.{u}` at arbitrary universe `u`. Every
specified smooth affine integral group model `P` over the maximal-unramified
integer ring of a nonarchimedean local field `F`, with specified generic group
`G` extended from `F`, has exact recovery from a finite Galois unramified
intermediate field. No stability assumption on integral points is needed for
this finite-coefficient construction.

The coefficients in the conclusion are the actual spectral integer ring
`extensionIntegers F E` of the finite field `E`. The recovered model uses
`IntegralModel.baseChange` along the actual field inclusion into the inertia
fixed field and `spectralIntegerInclusion` on integers. Its compatible
`IntegralModel.Iso` to `P` uses `finiteInertiaGenericIso`, the prescribed
canonical comparison with the extension of `G`. Thus the conclusion preserves
`P.genericIso`, rather than only identifying its underlying integral group.
The precise existential conclusion is `HasFiniteUnramifiedRecovery F G P` as
defined in `FiniteRecoveryInterface`.

`finiteRecoveryModel` constructs the finite integral model from two explicit
intermediate fields `K ≤ E`, a smooth affine group `H` over the integers of
`K`, and a generic isomorphism over `E`. Its group is the pullback of `H` along
`stageIntegerMap F h`. Affineness, flatness and finite type follow by base
change; smoothness of `H` supplies the latter two properties. Its generic
identification is exactly `rawStageGenericIso`: the enlargement square,
followed by the inverse supplied generic isomorphism and the field pullback
comparison to `G_E`. This definition does not assert the existence of its
inputs.

`finiteStage_baseChangeGenericIso` identifies the generic isomorphism used by
`IntegralModel.baseChange` with `inertiaGenericSquare` followed by the
pullback of the finite model's original generic isomorphism. It specializes
`baseChangeGenericIso_eq_square`; the comparisons agree by reflexivity. A
private reflexivity lemma similarly identifies `finiteInertiaGenericIso`
with the explicit field pullback comparison. A private adapter uses these
identities to package a square-coordinate generic compatibility equation as
an actual compatible model isomorphism.

`finiteRecoveryAt_of_rawStage` applies that adapter to `finiteRecoveryModel`.
Its inputs include an integral-group isomorphism from `P.group` to the
extension of `H` and an exact recovery equation for the generic isomorphism
over `E`. The integral isomorphism back to `P` is
`stageIntegralComparison` followed by the inverse supplied integral-group
isomorphism. The imported theorem `rawStage_generic` proves precisely its
generic compatibility; the two comparison identities above put that equation
in the coefficient-base-change conventions used by `HasFiniteRecoveryAt`.

Finally, `finiteUnramifiedRecovery` obtains a finite smooth affine spectral
model of `P.group` using `spectralGroupModel`. It obtains an enlarged finite
Galois unramified field and a generic isomorphism recovering the specified
one using `nonempty_modelIsoStage`. It unpacks both records before installing
the canonical coefficient algebras, applies `finiteRecoveryAt_of_rawStage`,
and packages the field's finiteness, Galois, inertia-containment and arithmetic
unramified witnesses. The `IsoStage.recovery` field is exactly the generic
recovery equation required by that adapter after unfolding
`stageGenericComparison`.

The provenance is internal: the construction combines the finite smooth
spectral model, descent of a specified generic isomorphism, and the proved
comparison coherences. These results are imported by their Lean names. This
unit discharges the finite-recovery input of the existing final assembly; the
smooth unramified descent theorem itself is assembled in a separate proof
module using the smooth homomorphism extension theorem as well.
