# From etale-local ambient conjugators to radical conjugators

Worker 593.

This internal algebraic reduction defines `EtaleLocallyRangeConjugate l l' T`
as existence of actual points of the ambient group on an etale cover of `T`
which satisfy the all-test range conjugator predicate. The cover index
universe is a parameter. The definition does not assert local existence.

Suppose multiplication of `l` and a normal subgroup `s` is an isomorphism,
and `range s` is contained in the specified `range r`. An ambient conjugator
on any test scheme `T` gives equality of the conjugated ranges over
`T.left` by the categorical comparison. Base change preserves the
multiplication isomorphism, normality and range containment. The existing
normal-factor reduction over that new base produces a section of the
pulled-back `s`. Range containment lifts its image to an actual section
of the pulled-back `r`. The pullback-point equivalence then gives an actual
point of `U` over `T`, and the radical range comparison proves that it is
an all-test radical conjugator. There are no monomorphism or geometric
hypotheses in this conversion.

Applying the conversion separately on each member of the same cover gives
`etaleLocallyRadicalConjugate_of_range`. No new cover or local choice
compatibility is required at this stage.

For a relative Levi, its multiplication witness may use a radical `s`
different from the specified `r`. The relative wrapper explicitly assumes
the entire `RelativeUnipotentRadicalStatement`. Over the original base,
this proposition identifies their all-test ranges. The multiplication
witness and normality of `s` then give the conversion above without
transporting any relative geometric predicate to `T`.

The last theorem combines this conversion with the conditional relative
descent theorem. It concludes the exact global range equation and uniqueness
appearing in `RelativeLeviConjugacyStatement`, but still assumes both entire
geometric propositions `RelativeUnipotentRadicalStatement` and
`RelativeLeviSelfNormalizerStatement`, as well as etale-local ambient
conjugacy. It does not establish the unchanged unconditional target.

The provenance is internal composition of the multiplication decomposition,
normal-factor conjugacy reduction, actual pullback-point equivalence, range
base change and effective descent. No new geometric assertion or axiom is
introduced.
