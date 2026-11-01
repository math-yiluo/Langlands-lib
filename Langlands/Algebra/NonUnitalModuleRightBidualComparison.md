# Actual right categorical bidual comparison

This is a derived internal comparison implementing the two contravariant dual
functors in Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, I.4.1, printed pp.22–23 / PDF pp.28–29
(`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The original nonunital conventions are printed pp.5–7 / PDF pp.11–13;
canonical complex scalars are in I.2.1, printed p.14 / PDF p.20.
The registered 2010 corrections, PDF pp.1–2
(`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`),
concern nearby injection, reflexivity and exactness arguments. The 2026 edition
governs. Worker 1149 specializes and extends Worker 6's comparison audit.

For an original right module, the first raw dual has an action of the double
opposite ring. `rawFirstDualAction` names this action. `firstDualAction`
transports it to the actual left A-action, and
`firstDual_isNondegenerate` transports its fixing idempotents.
`RightBidual` then takes the nondegenerate dual using the canonical complex
module recovered from that transported action. `rightBidualAction` and
`rightBidual_isNondegenerate` give its original right action and nondegeneracy.
`firstDualCanonicalModule_eq` identifies the complete recovered complex module
with the one recovered from the raw first-dual action, by the full-dual
comparison's scalar uniqueness argument.

`genericRightBidual_eq_raw` and `genericRightBidualAction_eq_raw` identify the
published opposite-ring bidual and its action with the raw comparison side.
`comparisonHom` and `comparisonInvHom` specialize the subtype comparison to the
first right dual. They are mutually inverse original right intertwiners, with
whole-map inverse identities. Their `val` laws identify the full-functional
comparison in both directions; their `val_coe` laws preserve the entire
underlying function. `comparisonLinear` packages the same equivalence for
exactly the two recovered right complex modules. Its entire additive map is
the additive map of `comparisonHom`.

`rightDoublePullback` transports the first right pullback to a left intertwiner
before the second pullback. Its `val` law exposes the actual second full
pullback. `genericRightDoublePullback_eq_raw` identifies the published generic
map with the raw counterpart. `comparison_naturality` is equality of whole
original right intertwiners at independent source and target universes. Its
proof specializes the subtype comparison's contravariant cross-naturality
to the first pullback and reverses the resulting equality.

`actualRightBidualFunctor` is definitionally exactly
`(rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA`.
The object-carrier, object-action and map-Hom laws identify this categorical
composite with `RightBidual`, `rightBidualAction` and `rightDoublePullback`.
`actualComparisonHom` and its inverse are definitionally the original
comparison maps. `actualComparison_naturality` exposes equality of whole
categorical underlying intertwiners. `comparisonNatIso` packages them using
`NatIso.ofComponents`; its inverse laws and naturality are the original-map
laws just described. The component laws expose both entire underlying maps
and their identity-on-functions formulas.

The companion Checks pair assigns complete unapplied interfaces at independent
algebra/carrier universes, specializes to both unequal algebra/carrier
directions and unequal source/target universes, and explicitly pins actions
and recovered complex modules in the presence of competing instances.
No complex module on an original carrier, comparison certificate, dimension
bound, nonzero condition, anti-involution or faithful action is assumed.
The generic bidual is imported by Lean name from its published construction;
evaluation transport is a separate successor pair.
