# Countable bases from actual function-field arithmetic

`Langlands.Global.functionFieldAdelesSecondCountable` proves the exact
`Langlands.Global.FunctionFieldAdelesSecondCountableStatement`, in an
arbitrary common universe for the finite constant field `k` and function
field `F`. This is a derived arithmetic topology argument for the Conrad
program, rather than a transcription of a numbered source proof.

The implemented proof first makes `Polynomial k` countable through its
finitely supported coefficient representation. The numerator and
denominator representation is a surjection from pairs of polynomials
onto `RatFunc k`. Finite dimensionality then makes `F` countable, using
`Finsupp.Countable.of_moduleFinite`.

The union, over `x : F`, of the places at which `x` is nonintegral covers
`AlgebraicCurve.Place k F`: every proper valuation subring excludes an
element. Each member of this countable family is finite by the published
`curvePlaceFinitePoles`, whose `PerfectField k` premise is supplied by
Mathlib's instance `PerfectField.ofFinite` for the finite constant field.
Thus the actual place type is countable. The injectivity of the published
`realAbsoluteValuePlaceCurvePlaceEquiv` transfers this result to the
quotient of all nontrivial real absolute values.

Density of `F` in the actual adic completion gives separability. For
second countability the proof chooses a rank-one structure for the
completed discrete valuation with real base `2`, then uses
`Valued.toNormedField`. This norm preserves the existing uniform space
by construction. Separability in that existing topology therefore gives
second countability without replacing the topology. The compatible
norm is local to the proof and adds no assumption to the statement.

For the actual curve-place adelic ring, the proof applies the published
`restrictedProduct_secondCountableTopology` to these countably many
second-countable local factors and their open integer subrings. For each
absolute-value place, the proof assembles a homeomorphism from the
published ring isomorphism `functionFieldAbsoluteValuePlaceCompletionEquiv`
and its two published continuity theorems; it transfers the local
conclusion to the actual absolute-value completion. The published
`functionFieldAbsoluteValueAdeleHomeomorph` likewise transfers the global
conclusion to the actual absolute-value adelic ring. Each finite-level
subring has the inherited subspace topology, so the explicit subtype
second-countability theorem gives the remaining conclusions.

No separability hypothesis on the rational-function presentation, residue
finiteness, or local compactness is assumed. The result does not prove
the remaining scheme or algebraic-space point comparisons, model
descent, compact quotient, or whole-paper assertions.
