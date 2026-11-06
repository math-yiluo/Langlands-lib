# The integral Harris order on carried Tate submodules

Author: Worker 344.

This internal construction equips the submodule carried by an original Harris
fixed level with a ring action of the unchanged integral Harris order. Its
operators are restrictions of the given rational action on the actual Tate
carrier. It proves the requisite source-span preservation and frame
intertwining rather than assuming integrality of the rational action.

## Inputs and scalar conventions

The number fields, algebra, schemes and point fields have universe zero. The
arithmetic data are the displayed totally real `E`, totally complex quadratic
extension `F`, central simple unitary datum `D` on `A`, signature charts `C`,
and algebra and scalar-tower instances. No division, CM-section specialization,
or algebraic closedness hypothesis is added. The source-only declarations
need the scalar towers displayed before the first namespace ends. The later
Harris fixed-level construction retains the surrounding scalar-tower context.

Write `O = D.harrisHodgePELIntegralOrder C`, `Af = Global.FiniteAdeles ℚ`,
`Rf = Global.integralFiniteAdeles ℚ` and `Vf = Af ⊗[ℚ] A`. These are the
existing positive-involution integral order and actual finite-adele rings.
The source span is exactly `D.harrisHodgePELIntegralAdeleSpan C`, generated
by `1 ⊗ x` for `x` in the integer Harris pairing lattice.

For target constructions, `P : Prerequisites` supplies the named geometric
prerequisites of `PositivePolarizedAction`; the base `S` is quasi-separated
and `s : Spec Ω ⟶ S` is a field-valued point. The finite Weil-transition
statement and rational profinite-integer/finite-adele comparison `h` remain
explicit. Compatible frames retain `auxiliaryStarRing D C` and the original
Harris form. The target `Rf`-module is restriction of its actual finite-adelic
Tate module along the integral subring inclusion. The rational Tate carrier
always uses the full index predicate `fun _ => True`.

## Preservation of the actual source span

`CentralSimpleUnitaryData.harrisIntegralAdeleOrderAction` is a ring
homomorphism from `O` to the `Af`-linear endomorphisms of `Vf`. It composes
the integral order inclusion, the tensor-algebra inclusion `a ↦ a ⊗ 1`, and
the existing `scalarExtensionAlgebraAction`. Its pure-tensor formula is
`r ⊗ x ↦ r ⊗ (a * x)`, proved by the published tensor-action formula in
`harrisIntegralAdeleOrderAction_tmul`.

`harrisIntegralAdeleOrderAction_mem` proves preservation of the actual
integral source span. On a generator, it applies the existing
`harrisHodgePELIntegralOrder_mul_mem_integralLattice` and includes the
resulting tensor in the span. Span induction handles zero, addition and
`Rf`-scalars, using the operator's actual `Af`-linearity for the latter.
No stronger order, different lattice, or presumed integral Tate action is
substituted for the existing inputs.

## Actual rational Tate operators and frame images

`harrisIntegralTateOrderOperator X a` is the actual
`Tate.finiteAdeleHomMap` of the supplied rational endomorphism
`X.actionObj.action a`, restricted to `Rf`-scalars. Its underlying function is
the unchanged `Tate.rationalHomMap`. `harrisIntegralTateOrderAction X`
packages these operators into a ring homomorphism. The zero, one, addition
and multiplication laws follow by evaluating the original algebra action
and `Tate.rationalEndAction`, both already algebra homomorphisms.

`harrisIntegralFrame_order` proves that a supplied compatible frame
intertwines the source order action and these target operators. It evaluates
the original frame's tensor-algebra linearity at `a ⊗ 1`. The actual target
tensor action is the rational endomorphism action composed with the
finite-adele action of one; the latter is the identity. This gives equality
of the actual vectors, not only of their classes.

`harrisIntegralFrameLattice_order_mem` writes a member of the carried frame
submodule as the image of a source-span member. Intertwining and source-span
preservation then put its image under every order element back in that same
submodule. `harrisIntegralFrameLatticeOrderAction` restricts the ambient ring
action to this submodule. Its ring laws follow from the ambient ring laws by
linear-map extensionality. `harrisIntegralFrameLatticeOrderAction_apply`
identifies the inclusion of every resulting vector with the original actual
rational Tate homomorphism map; the equality is reflexive.

## The original fixed level

The final declarations additionally retain finite fibres at `s` for every
finite-etale cover, the torsion finite-etale statement, invertibility of every
positive torsion index, and the finiteness and etaleness instances for all
corresponding roots-of-unity schemes. The level object is the existing
`PolarizedWeilLevel.levelTower` with its original geometrically fixed right
orbits. The level subgroup `K.toSubgroup` is assumed contained in
`harrisIntegralAdeleStabilizer D C`, exactly as required to define the carried
level submodule. There is no normalization hypothesis.

`harrisIntegralLevelLattice_order_mem` chooses a representative solely to
prove preservation, rewrites the already defined level submodule as that
representative's frame image using `harrisIntegralLevelLattice_eq_frame`,
and applies the frame preservation theorem.

`harrisIntegralLevelLatticeOrderAction X K hK x` itself makes no choice of
frame: it restricts `harrisIntegralTateOrderAction X` to the already defined
`harrisIntegralLevelLattice X K hK x`. The preservation proof supplies the
restriction, and the four ring laws descend from the ambient ring
homomorphism. Its application formula, proved by reflexivity in
`harrisIntegralLevelLatticeOrderAction_apply`, is exactly the original
rational Tate map of `X.actionObj.action a` after inclusion in the ambient
carrier. The action is thus on the original orbit's carried submodule,
independent of the representative used in its preservation proof. The
original opposite-group right-action convention is retained through that
unchanged orbit and submodule.

## Provenance and limits

The provenance is internal. The unit derives these actions from the published
Harris order preserving the integer pairing lattice, the actual tensor and
rational Tate algebra actions, compatible-frame linearity, and the carried
submodules. No new literature theorem or existence assertion is invoked.

These operators are endomorphisms of an integral-adele submodule of the
rational Tate space. They are not asserted to be morphisms of abelian
schemes. The unit supplies neither finite generation, freeness, topology,
commensurability nor realization of that submodule by an isogenous model.
Such realization, descent of the rational order action to actual scheme
endomorphisms, polarization and determinant compatibility, normalized-model
existence and the exact division representability theorem remain obligations
of the subsequent construction.
