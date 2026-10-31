# Actual pointed pullback of a positive Harris polarized action

`framedPositiveActionBaseChange` constructs an actual
`PositivePolarizedAction` over the changed base. The source is an
existing positive Harris polarized action `X/S`, an actual map
`b : T ⟶ S`, and an actual point `t : Spec Ω ⟶ T`. The arithmetic
fields, algebra, schemes and point field have universe zero.

The new action object is precisely
`(RationalAlgebraAction.pullback b).obj X.actionObj`. Its abelian
scheme is the actual geometric pullback of the original abelian
scheme, and its rational action is
`(rationalBaseChangeEnd b X.actionObj.abelianScheme).comp X.actionObj.action`.
No output abelian scheme or output action is supplied as data.

The new dual is `dualAbelianSchemeFromEvaluation` on this actual
changed abelian scheme with the displayed `HasDualScheme`,
`DualSchemeGeometry`, inverse Poincare line bundle and actual
tensor evaluation isomorphism. Its endomorphism dual-map
additivity is also explicit. These are construction data of that
dual, not arbitrary output geometry or a polarization map.

The polarization map is exactly `dualAbelianBaseChangeMap` applied
to `X.polarization`, using the published
`dualAbelianBaseChange` proof of canonical comparison group
compatibility. Thus it is actual integral pullback followed by
the prescribed Poincare-compatible comparison. Preservation of
the full relative polarization predicate is obtained from the
explicit named `PolarizationBaseChangeStatement` input. That
input includes the actual isogeny and every-geometric-fibre
ample-Mumford conditions; this construction does not prove it.

Faithfulness is proved using only existence of an actual full
adelic frame on the regular Harris source at `t ≫ b`, together
with the explicit rational finite-adele comparison. The
`HarrisAdelicFrameFaithfulness` theorem transports such a frame
by the existing pointed frame comparison. The constructed
nondegenerate source form gives a nonzero vector, the unital
actual Tate action makes the changed rational endomorphism ring
nontrivial, and simplicity of the same Harris algebra gives
injectivity of the changed rational action. No assertion of
faithful pullback over arbitrary unpointed or empty bases is
assumed.

The involution equation uses the same positive auxiliary left
involution from `auxiliaryStarRing D C` at both bases. It follows
from `IsInvolutionCompatible.baseChange_of_naturality` applied to
the original equation and the explicit named
`DualAbelianBaseChangeNaturalityStatement`. The integral recovery
formula for `rationalDualBaseChangeHom` identifies its map with
the rational inclusion of the exact new integral polarization.
The construction retains all seven tensor/Picard inputs, the
Mumford square input and universal-family base-change input.

The fields for the action object, integral polarization and displayed
dual witnesses are assigned exactly these constructions. The
constructor proves the full polarization, injectivity and involution
fields by the arguments above. The auxiliary StarRing is bound
explicitly before all dependent endpoint inputs, so their field
projections use precisely the same constructed involution.

The provenance is internal: Worker 57 combines the existing
actual action pullback and canonical integral dual transport
with the conditional involution theorem, named whole
polarization stability and the proved pointed Harris
faithfulness argument. The naturality and polarization
statements remain separate proof obligations, not new axioms.

This construction supplies no frame existence, endpoint dual
existence or geometry theorem, identity or successive-base
comparison of polarized objects, level transport, rational-isogeny
quotient functor, moduli representability, coefficient descent or
scheme level. Those require the additional owned comparisons
and existence results. The output object is concretely
constructed under the displayed premises; it is not a completed
varying-base PEL moduli functor.
