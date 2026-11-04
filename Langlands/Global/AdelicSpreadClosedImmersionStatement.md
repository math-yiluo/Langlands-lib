# Closed embeddings on actual generic-fiber adelic points

`Langlands.Global.AdelicSpreadClosedImmersionStatement` conjoins the
function-field and number-field assertions that a closed immersion of field
schemes induces a closed embedding on their actual full-adele points. The
topologies on source and target come from independently specified finite-type
arithmetic spreads. The two constituent propositions are
`CurvePlaceSpreadClosedImmersionStatement` and
`NumberFieldSpreadClosedImmersionStatement`. All types share arbitrary
universe `u`.

In the curve clause, `k` is a perfect field, `F` carries its original `k`-algebra
structure and specified `RatFunc k` action with the compatible scalar tower,
and `FunctionField k F` says that `F` is finite over that rational-function
field. The models `X` and `Z` lie over the actual rings of integers outside
arbitrary finite sets `S` and `U` of places. Their structure maps are locally
finite type and quasi-compact. The displayed generic-fiber isomorphisms
identify their actual pullbacks to `F` with `Y` and `W`. The arbitrary morphism
`g : Y ⟶ W` is assumed to be a closed immersion. Its map on points is literal
postcomposition of relative scheme morphisms with `g`. The two explicit
topology arguments are exactly `curvePlaceSpreadAdelePointTopology` for the
two specified spreads.

The number-field clause uses the original number field `K`, actual outside-set
integer rings, actual pullbacks and the actual full adele ring `Adeles K`,
including every infinite place. It has the corresponding independent finite
sets, models, finite-type hypotheses, generic-fiber isomorphisms and closed
immersion. It uses exactly the two displayed
`numberFieldSpreadAdelePointTopology` structures. Neither clause assumes that
the given spreads already carry a model of `g`, or that a descended model
morphism is already closed. No affineness, separatedness or quasi-separatedness
is imposed on the models or the field schemes.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p. 9, Section 4, first two paragraphs. The assertion
that closed immersions give closed embeddings precedes the separatedness
restriction there. Printed pp. 5–6, Theorem 3.4(1)–(3) and equation (3.5.1),
provide the model descent, eventual closed immersion and comparison framework.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The arbitrary perfect constant field, possibly inseparable function-field
extension, and empty initial place sets are derived extensions of the global-field
formulation. The proof route uses noetherianity of the actual integer rings
to obtain finite presentation, actual model-morphism descent, eventual
closed-immersion descent, and the fixed-model final-topology closed-embedding
result. Naturality of the actual point equivalences and independence of the
spread topology transfer that result to the two originally specified spreads.
The number-field convention always retains all infinite factors.

This file states propositions only. Its publication supplies neither their
proof nor existence of a spread for an arbitrary field scheme. The remaining
topological properties and whole-paper coverage remain separate obligations.
