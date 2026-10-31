# Harris–Taylor numerical pullback and actual moduli presheaf

Author: Worker 57.

This internal construction proves arbitrary-base-change stability of the
existing Harris–Taylor central trace and numerical tests and constructs
the corresponding presheaf of actual rational algebra-action classes.
The exact named `LieBaseChangeNaturalityStatement` remains an explicit
hypothesis. No proof of that integral proposition is supplied here.

The fields, rational algebra, and arithmetic central trace formula are
the existing ones in `HarrisTaylorLieCondition`. Schemes have universe
zero, as in that source-specialized module. The local trace predicate
uses the actual rational algebra action restricted to the actual CM
centre and the prescribed arithmetic section through the same structure
map to the CM spectrum.

The overlap theorem applies intrinsic trace independence to two finite
Lie charts on a common smaller open. The cover theorem applies actual
structure-sheaf separation, using the already proved restriction laws
on both sides of the central identity.

`centralAction_baseChange` identifies restriction of the actual
pulled-back rational algebra action with pullback of the restricted
central action. Conditional rational Lie trace pullback and the
existing arithmetic-section pullback law therefore prove the local
trace identity in the constructed inverse-image chart.

For the all-chart theorem, inverse images of the actual finite local
Lie trivializations cover the target. The local pullback theorem proves
the test in those charts. Restricting to intersections, changing the
finite chart by the overlap theorem, and applying sheaf separation prove
the test on every smaller open of every target chart. The scheme
morphism is arbitrary; there is no flatness, reducedness or affineness
requirement.

`numericalCondition_baseChange_of_naturality` combines that all-chart
trace theorem with the existing base-change theorem for the actual
geometric relative dimension. Thus it preserves both conjuncts of the
existing numerical condition on the same actual pulled-back abelian
scheme and its actual rational action.

The well-defined central trace quotient predicate survives the existing
actual class pullback. The numerical class predicate is the existing
image of actual satisfying representatives. Its pullback theorem pulls
back a satisfying representative and uses the actual class formula.
It does not assert that the geometric dimension condition is invariant
under every equivariant rational isomorphism. In particular, the
existing existential interpretation of numerical classes is preserved.

With an explicit family of the named integral naturality statements,
`numericalActionSubfunctor` restricts the existing presheaf of actual
rational algebra-action classes on schemes over the actual CM spectrum.
The over-category triangle and the proved numerical class stability
establish closure under every morphism. `numericalActionPresheaf` is its
actual subtype presheaf; its identity and composition laws come from
`Subfunctor.toFunctor` and the previously constructed class presheaf.
The object formula identifies its values with the existing
`NumericalActionClass`. The map and representative formulas retain the
actual abelian-scheme pullback and its rational endomorphism action.
The natural inclusion is injective at every object.

The provenance is internal: actual local matrix and trace transport,
canonical rational Lie compatibility under its named hypothesis, the
existing arithmetic-section and geometric-dimension pullback theorems,
and sheaf separation. The underlying arithmetic formula and numerical
test retain their existing source provenance. No new external theorem,
Lie-plus equivalence, polarization or level structure, full PEL moduli
functor, representability or scheme level is asserted by this module.
