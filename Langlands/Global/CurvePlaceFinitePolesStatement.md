# Finite poles on actual function-field curve places

`Langlands.Global.CurvePlaceFinitePolesStatement` states that, for a perfect
field `k` and a function field `F` of one variable over `k`, every element of
`F` belongs to the valuation ring at all but finitely many concrete curve
places. All types lie in a common arbitrary universe `u`.

The field `F` carries a specified algebra structure over `RatFunc k`, finite
dimensionality over that rational function field, a `k`-algebra structure and
the compatibility `IsScalarTower k (RatFunc k) F`. No separability condition
is imposed on this specified rational-function-field extension. The
perfectness assumption on the constants includes every finite field, so the
target includes global function fields even when the specified rational
parameter gives an inseparable extension.

The places are the published `AlgebraicCurve.Place k F`: proper principal
valuation subrings of `F` containing the image of `k`. Membership in
`v.toValuationSubring` is literal membership in that subring of `F`. The finite
set in the conclusion consists of the places where the given field element
is not integral. There is no assumed finite-support condition on that
element. In particular, the statement includes `0`.

This is a derived arithmetic prerequisite for the adelic construction in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December
31, 2011), printed p.1: the global field acts on its adele ring, whose open
levels impose integrality outside finite sets of places. The paper uses this
arithmetic background rather than stating the present perfect-constant-field
generalization as a separate theorem. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

This file supplies a proposition target, with proof publication a separate
milestone. It does not construct the full-field diagonal, identify these
concrete places with any alternative convention for global places, prove
local compactness of completions, or compare geometric adelic point spaces.
Those obligations remain part of the whole-paper program. Conrad's
nonempty convention for the finite all-place set is also separate from the
finite set of poles asserted here, which may be empty.
