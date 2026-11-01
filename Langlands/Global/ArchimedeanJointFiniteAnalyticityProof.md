# Real analyticity from genuine joint differential finiteness

`Langlands.Global.ArchimedeanGL.jointFiniteAnalyticity` proves the exact
`JointFiniteAnalyticityStatement K n` for an arbitrary number field in an
arbitrary universe and every natural rank, including zero. A smooth
complex-valued function with finite-dimensional genuine joint central and
full compact differential orbit has a real analytic coordinate extension
at every actual archimedean unit. The original ambient matrix norm and
topology are retained, including all real directions at complex places.

The proof obtains a monic annihilating polynomial of the actual Cartan
square-sum action from the finite joint orbit. The coordinate realization
of this polynomial supplies its complete scalar differential operator,
analytic coefficients, equality of the full action on smooth coordinate
extensions, and its principal symbol. On the open range of the units,
this symbol is a power of the strictly positive real Cartan covector
form, hence is nonzero on every nonzero real covector.

The annihilating equation follows from action equality, the actual
coordinate-extension identity, and membership of the original function
in its joint orbit span. Apply the proved scalar analytic elliptic
regularity theorem to this equation on the open unit range, then evaluate
at each unit. No estimate, ellipticity certificate or regularity theorem
is assumed in the result's telescope. Two examples check the full
universe-general telescope and its rank-zero specialization.

The proof uses the published theorems
`cartanSquareSumPolynomialAnnihilation`,
`cartanPolynomialCoordinateRealization` and
`Langlands.Analysis.scalarEllipticAnalyticity`, imported by Lean name.
The unit range contains every actual unit, so the argument applies in
every component. The scoped order `∞` in `ContDiffOn ℝ ∞` means
smoothness. Neither the rank, the function nor the annihilating
polynomial's degree is required to be positive. The scalar theorem
includes zero dimension and zero order.

This implements the local elliptic route of Harish-Chandra, *Two theorems
on semi-simple Lie groups*, section 17, Lemma 33, printed pages 108–109
(one-based PDF pages 35–36), with section 16, printed page 106 (PDF
page 33); registered source
`provided-3315156dfd5120bb69df4005d1cb66c074532e8f8ab3cd2459c5990658370e91`.
The companion route is *Discrete series for semisimple Lie groups II*,
sections 7–8, printed and one-based PDF pages 15–19, especially the proof
of Theorem 1 on page 18; registered source
`harish-chandra-1966-discrete-series-ii`. The first source uses a subgroup
containing the center and compact modulo the center; the second uses an
actually compact subgroup. This formal result is an internal smooth
matrix specialization with stronger compact-direction finiteness.
It uses no global Cartan decomposition or component bridge.

The scalar regularity input follows the derived Morrey–Nirenberg route
recorded in `notes/automorphic/elliptic-analyticity-source-map.md`.
Its published proof module documents the weighted elliptic estimate,
the passage through local Sobolev bounds to pointwise factorial bounds,
the analyticity criterion, the zero cases and the actual finite-basis
coordinate transport. This final assembly imports that unconditional
scalar theorem and changes none of its hypotheses or constructions.

Worker 116 wrote this final Lean and Markdown pair and developed the
coordinate realization, weighted analytic bridge, zero cases and
coordinate transport in separately published work. Worker 94 developed
the actual Cartan annihilator and the variable coefficient weighted
factorial estimate. Worker 815 developed analytic coefficient bounds,
the weighted cutoff recurrence, local Sobolev estimates and the
factorial analyticity criterion as the coordinated analytic part of
this task. These mathematical contributions are credited to Workers 94,
815 and 116; the focused publications retain their own authorship.
Worker 1130 assembled the separately published scalar regularity
submission and rewrote its documentation.

This module compiles at default heartbeats, including the complete
arbitrary-universe and rank-zero examples. The theorem uses only
`propext`, `Classical.choice` and `Quot.sound`. The target statement's
Lean/Markdown pair and all pairs in its import closure are unchanged.
