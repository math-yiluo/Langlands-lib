# Point comparison of selected original Harris level orbits

This internal construction compares the original direct Harris test levels
whose raw evaluation belongs to a selected base monodromy orbit. The comparison
is the restriction of the existing fixed-level point isomorphism. Its orbit
condition, evaluation square and compatibility with every original level
transporter are proved using actual Tate path transport.

The namespace is
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`. The arithmetic carriers,
schemes and endpoint fields in this file are in universe zero.

## Supplied data and conventions

Fix the totally real number field `E`, its totally complex quadratic extension
`F`, the central simple unitary datum `D` on `A`, the auxiliary quadratic CM
field `L`, its map to `F`, and the normalized Harris signature charts `C`.
The named scalar structures and towers are those of the imported Harris
constructions. Fix `P : Prerequisites`, an abelian scheme `B` over `S`, an actual
`DualWitness W`, a morphism `lam : B ⟶ W.dual P`, a quasi-separated object
`T : Over S`, and an integral order action `a` on the actual pullback of `B`
to `T`. The finite Weil transition statement and the rational/profinite
integer-adele comparison are supplied. This file does not require a separate
proof that `lam` is a polarization or that `a` satisfies the full CM condition.

Write `H` for `ScalarExtensionSimilitudes` of the unchanged Harris Hodge PEL
form. Its right action on actual Weil frames uses `Hᵐᵒᵖ`, as in the original
constructions. For a subgroup `U ≤ H`, the raw set at a point is `RightOrbit`
of those frames by `U`; it is a quotient by right precomposition. Monodromy
acts on that quotient because the actual frame actions commute.

For the raw transport results, supply two points `s` and `r` of `T.left`
over possibly different fields, their finite-fibre witnesses, a fibre-functor
isomorphism `path`, `TorsionFiniteEtaleStatement`, invertibility on `T.left`
of every positive indexed torsion order, and finite and etale roots of unity
at all those orders. All these hypotheses are explicit. The paths are supplied,
so these results impose no connectedness, local Noetherianity or algebraic
closure assumptions.

For the selected-level comparison, supply an arbitrary morphism
`f : T' ⟶ T` in `Over S`, with both underlying test schemes quasi-separated.
Supply points `t` and `u` of `T'.left`, their finite-fibre witnesses and a path
between their fibre functors. The base points are literally `t ≫ f.left` and
`u ≫ f.left`, with their own finite-fibre witnesses. The actual base path is
`pathPushforward f.left htf huf path`. The torsion-order and roots-of-unity
hypotheses are supplied on both tests. No finiteness or etaleness condition is
placed on `f`. The action on the direct restricted family is exactly
`(relativeEndRestrict B f).comp a`.

## Raw path transport and monodromy

The raw equivalence used throughout is the imported
`harrisIntegralCMWeilRawPointEquiv`. It descends actual
`Tate.weilAdelicFrameTransport` to the original right-orbit quotients.

`harrisIntegralCMWeilRawPointEquiv_translate` proves that this equivalence
commutes with every right level transporter `g` satisfying
`g⁻¹ * U * g ⊆ V`. Quotient induction reduces the claim to a frame
representative. Subtype and linear-equivalence extensionality then reduce it
to the definitional identity that Tate transport commutes with precomposition
of the frame.

`harrisIntegralCMWeilRawPointEquiv_monodromy` proves equivariance for the
actual fundamental groups. A source loop is sent to the target loop by
`pathConjugation path`. Quotient induction applies the published
`Tate.weilAdelicFrameTransport_monodromy` equality to a frame representative.

`harrisIntegralCMWeilRawPointEquiv_mem_orbit_iff` proves
preservation and reflection of membership in a selected monodromy orbit.
In the reverse direction of transport, surjectivity of the actual group
isomorphism `pathConjugation path` supplies a source loop, and injectivity of
the raw equivalence reflects the equality. In the forward direction, the
preceding equivariance theorem transports the witnessing source loop.
This is a result for all raw right-orbit classes, without a monodromy-fixedness
assumption.

`harrisIntegralCMWeilRawPointEquiv_change_path` identifies the actual change
under two paths with the target loop `path.symm ≪≫ path'`:
transport along `path'` of a raw class is that loop acting on transport along
`path`. Quotient induction and frame extensionality reduce the formula to
`Tate.rationalTransport_change_path` at each Tate value.

Consequently,
`harrisIntegralCMWeilRawPointEquiv_orbit_path_independent` proves equality of
the two selected target monodromy orbit sets by `MulAction.orbit_smul`.
Individual raw classes can still depend on the path.

## Selected original test levels

At a Harris level `V`, let `ev_t` be the existing
`harrisIntegralCMRestrictionRawClass` for `f`, evaluated at `t`, with its
base point taken to be the literal composite `t ≫ f.left`. For a base raw
class `q`, the selected type is

```text
{ l : original direct fixed levels at t and V //
    ev_t(V, l) belongs to the base fundamental-group orbit of q }.
```

`harrisIntegralCMTestLevelOrbitPointEquiv` gives an equivalence from this
type to the corresponding selected type at `u`, with selected base class
the actual raw transport of `q` along the pushed path. It is defined by
`Equiv.subtypeEquiv` on the original
`harrisIntegralCMFullActionLevelPointIso`. The predicate equivalence is proved:
the published `harrisIntegralCMRestrictionRawClass_pointMap` identifies the
actual evaluation of the transported fixed level, and the raw
orbit-membership equivalence above preserves and reflects its orbit condition.
The desired predicate equivalence is not an extra input.

`harrisIntegralCMTestLevelOrbitPointEquiv_val` and
`harrisIntegralCMTestLevelOrbitPointEquiv_symm_val` identify the underlying
values with the original forward and inverse fixed-level maps. Both
equalities hold by definition of the subtype equivalence.

`harrisIntegralCMTestLevelOrbitPointEquiv_evaluation` proves that original raw
evaluation after this selected comparison equals base raw path transport
after original evaluation. It applies the published original evaluation
square to the unchanged underlying fixed level.

`harrisIntegralCMTestLevelOrbitPointEquiv_natural` proves the complete
selected-subtype square for every original arrow `j : V ⟶ Z` in
`HarrisLevel D`. The selected transition at each endpoint is the independently
defined `harrisIntegralCMTestLevelOrbitMap`, whose underlying value is the
original direct level-tower transition. An equation saying that original
right translation sends `q` to `r` is supplied at the source point. The
corresponding equation at the target point is proved within the statement
using the raw translation theorem; it is not another compatibility premise.
Subtype extensionality, the two value formulas and naturality of the original
point isomorphism establish the square.

Finally,
`harrisIntegralCMTestLevelOrbitPointEquiv_val_path_independent` proves
equality of the underlying original fixed-level outputs for any two supplied
paths. It uses the value formulas and the published
`harrisIntegralCMFullActionLevelPointIso_path_independent`.
The selected target predicates have equal orbit sets by the earlier raw
orbit-set theorem. The final theorem states equality of underlying values,
without silently identifying the two dependent subtype expressions.

The raw and value/naturality lemmas omit `IsCMField F` and
`IsScalarTower ℚ F A` where their proofs do not use them. The last
path-independence theorem retains both because its imported original
fixed-level theorem retains them.

## Provenance and scope

This is an internal deduction from the published actual frame transport,
restriction evaluation, original fixed-level point isomorphism and original
selected-level transition constructions. It introduces no external source
assertion, axiom or new geometric prerequisite. The proof steps described
above are the implemented Lean proofs.

The result compares the original orbit-valued test levels of a supplied
abelian family along supplied paths. It constructs no comparison between
the actual schemes chosen as orbit covers, and does not prove existence of
paths. Full normalized rational-isogeny comparison, determinant/Lie and
Rosati integration, and the existence, admissibility, smoothness and
projectivity of a representing PEL scheme remain separate obligations.
In particular, this file does not prove
`HarrisTaylorCMWeilLevel.DivisionCMRepresentabilityStatement`.
